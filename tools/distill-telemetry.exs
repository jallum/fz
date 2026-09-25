# Distill a `fz2 --log-telemetry` JSONL stream into where the time went.
#
# Spans carry timing: a `span_start` record names what began and a `span_stop`
# record carries `elapsed_ns` for the same `span_id`. Spans nest through
# `parent_span_id`, so a span's INCLUSIVE time contains its children and its
# SELF time is what it spent on its own. Both are summed here by span name and,
# for compiler jobs, by job kind and by the function the job served.
#
#     elixir tools/distill-telemetry.exs trace.jsonl [--top 20]

defmodule Distill do
  def main(args) do
    {opts, [path], _} = OptionParser.parse(args, strict: [top: :integer])
    top = Keyword.get(opts, :top, 20)

    records = path |> File.stream!() |> Stream.map(&JSON.decode!/1) |> Enum.to_list()
    names = names(records)
    spans = spans(records, names)
    wall = wall(records)

    IO.puts("#{length(records)} records, #{map_size(spans)} spans, #{fmt_ms(wall)} ms from first record to last\n")
    timeline(records, spans)
    by_name(spans, top)
    jobs = for {_id, %{name: "fz.compiler2.job"} = s} <- spans, do: s
    by_kind(jobs, top)
    job_census(jobs, top)
    by_subject(jobs, top)
    reruns(jobs, top)
    return_revisions(records, names, top)
    wakes(records, jobs, names, top)
  end

  # The compiler names each function once, in a canon event; jobs name it by id.
  defp names(records) do
    for %{"name" => ["fz", "compiler2", "canon", "function"], "metadata" => %{"function_id" => id, "canon" => canon}} <- records,
        into: %{},
        do: {id, canon}
  end

  # One map per span: name, label (what it was about), start, inclusive and
  # self time in nanoseconds.
  defp spans(records, names) do
    starts =
      for %{"kind" => "span_start", "span_id" => id} = r <- records, into: %{} do
        {id,
         %{
           id: id,
           parent: r["parent_span_id"],
           name: Enum.join(r["name"], "."),
           label: label(r["metadata"], names),
           start: r["time_ns"],
           inclusive: 0,
           self: 0
         }}
      end

    with_stops =
      Enum.reduce(records, starts, fn
        %{"kind" => "span_stop", "span_id" => id, "elapsed_ns" => elapsed}, acc ->
          Map.update!(acc, id, &%{&1 | inclusive: elapsed, self: elapsed})

        _, acc ->
          acc
      end)

    # A child's inclusive time comes out of its parent's self time.
    Enum.reduce(with_stops, with_stops, fn {_id, span}, acc ->
      case Map.fetch(acc, span.parent) do
        {:ok, parent} -> Map.put(acc, parent.id, %{parent | self: parent.self - span.inclusive})
        :error -> acc
      end
    end)
  end

  defp label(%{"job" => job}, names), do: {job["kind"], subject(job, names)}
  defp label(%{} = meta, _names) when map_size(meta) == 0, do: {nil, ""}
  defp label(meta, _names), do: {nil, inspect(meta, limit: 6)}

  # A job's subject, with a function named rather than numbered.
  # The function is what a reader looks for, so it leads; the remaining keys
  # follow in a fixed order so two rows for the same subject render alike.
  defp subject(job, names) do
    fields = Map.drop(job, ["kind", "opaque_type"])
    name = for {"function_id", id} <- fields, do: Map.get(names, id, "f#{id}")

    rest =
      fields
      |> Map.drop(["function_id"])
      |> Enum.sort_by(fn {k, _} -> k end)
      |> Enum.map(fn {k, v} -> "#{k}=#{inspect(v)}" end)

    Enum.join(name ++ rest, " ")
  end

  # How many rounds each activation's return type took. Every
  # return_type.defined is one strict ascent of the fixpoint's central fact,
  # and a return_type.widened says the ascent ran past its budget, so the
  # answer was widened rather than found.
  defp return_revisions(records, names, top) do
    IO.puts("return-type revisions per activation")

    widened =
      for %{"name" => ["fz", "compiler2", "return_type", "widened"], "metadata" => %{"activation" => a}} <- records,
          into: MapSet.new(),
          do: subject(a, names)

    defined =
      for %{"name" => ["fz", "compiler2", "return_type", "defined"], "metadata" => %{"activation" => a}} <- records,
          do: subject(a, names)

    defined
    |> Enum.frequencies()
    |> Enum.sort_by(fn {activation, n} -> {-n, activation} end)
    |> Enum.take(top)
    |> Enum.map(fn {activation, n} -> {activation, n, if(activation in widened, do: "yes", else: "-")} end)
    |> table(["activation", "revisions", "widened"])
  end

  # A job start whose subject already ran is a re-run; the first start for a
  # subject is not. `job_census/2` and `wakes/4` both key off this.
  defp reruns_by_label(jobs) do
    jobs
    |> Enum.group_by(& &1.label)
    |> Enum.filter(fn {_, ss} -> length(ss) > 1 end)
    |> Map.new(fn {label, ss} -> {label, length(ss) - 1} end)
  end

  # Every job kind's work: how many times it ran, how many distinct subjects
  # it ran for, the excess this leaves (runs a subject's first run didn't
  # need), and the worst single subject. A kind with zero excess runs exactly
  # once per subject; proportional compilation is excess staying at zero.
  defp job_census(jobs, top) do
    IO.puts("job runs vs subjects")

    rows =
      jobs
      |> Enum.group_by(fn s -> elem(s.label, 0) end)
      |> Enum.map(fn {kind, ss} ->
        counts = ss |> Enum.frequencies_by(& &1.label) |> Map.values()
        subjects = length(counts)
        runs = Enum.sum(counts)
        {kind, runs, subjects, runs - subjects, Enum.max(counts)}
      end)
      |> Enum.sort_by(fn {_, _, _, excess, _} -> -excess end)

    total_runs = length(jobs)
    total_subjects = jobs |> Enum.map(& &1.label) |> Enum.uniq() |> length()

    (Enum.take(rows, top) ++ [{"TOTAL", total_runs, total_subjects, total_runs - total_subjects, nil}])
    |> table(["kind", "runs", "subjects", "excess", "max runs/subject"])
  end

  # Why the most re-run jobs ran again: each work_graph.applied record lists
  # the jobs a completion woke and the fact that caused each wake. Grouped by
  # (job kind, changed fact + use, completing job kind, disposition) rather
  # than free text, so the same shape of cause across many subjects collapses
  # to one row instead of one row per subject.
  defp wakes(records, jobs, names, top) do
    IO.puts("cause of every re-run")

    reruns = reruns_by_label(jobs)
    total_reruns = reruns |> Map.values() |> Enum.sum()

    wake_rows =
      for %{"name" => ["fz", "compiler2", "work_graph", "applied"], "metadata" => %{"completion" => c}} <- records,
          wake <- c["wakes"] || [],
          target = {wake["job"]["kind"], subject(wake["job"], names)},
          Map.has_key?(reruns, target),
          do: {wake["job"]["kind"], wake["cause"]["kind"], wake["cause"]["use"], c["kind"], wake["disposition"]}

    {enqueued, coalesced} = Enum.split_with(wake_rows, fn {_, _, _, _, d} -> d == "enqueued" end)
    unattributed = total_reruns - length(enqueued)

    cause_table(enqueued, top)
    IO.puts("  coalesced: an additional cause landing on a re-run already enqueued by the row above, not a separate start")
    cause_table(coalesced, top)

    tally = work_start_tally(records)

    IO.puts(
      "  #{unattributed} re-run(s) with no matching enqueued wake " <>
        "(session-summed work starts: ignition=#{tally.ignition} " <>
        "changed_revision_wake=#{tally.changed_revision_wake} " <>
        "activation_frontier=#{tally.activation_frontier} " <>
        "blocked_waiter_expansion=#{tally.blocked_waiter_expansion} " <>
        "unsanctioned=#{tally.unsanctioned})"
    )

    IO.puts("")
  end

  defp cause_table(rows, top) do
    rows
    |> Enum.frequencies()
    |> Enum.sort_by(fn {_, n} -> -n end)
    |> Enum.take(top)
    |> Enum.map(fn {{kind, fact_kind, fact_use, completing, disposition}, n} ->
      {kind, "#{fact_kind} (#{fact_use})", completing, disposition, n}
    end)
    |> table(["job kind", "changed fact (use)", "completing job", "disposition", "count"])
  end

  # `pull.session.finished` carries one session's cumulative WorkStartTally;
  # summed across every session in the stream this is the whole run's
  # breakdown of why a job entered the agenda. `changed_revision_wake` is the
  # wake-caused path `wakes/4` explains one row at a time; the other three
  # reasons cover every job's first run plus any re-run this stream's wakes
  # cannot name (see `wakes/4`'s unattributed count).
  defp work_start_tally(records) do
    zero = %{ignition: 0, changed_revision_wake: 0, activation_frontier: 0, blocked_waiter_expansion: 0, unsanctioned: 0}

    for %{"name" => ["fz", "compiler2", "pull", "session", "finished"], "metadata" => %{"session" => s}} <- records,
        reduce: zero do
      acc ->
        %{
          ignition: acc.ignition + s["work_starts_ignition"],
          changed_revision_wake: acc.changed_revision_wake + s["work_starts_changed_revision_wake"],
          activation_frontier: acc.activation_frontier + s["work_starts_activation_frontier"],
          blocked_waiter_expansion: acc.blocked_waiter_expansion + s["work_starts_blocked_waiter_expansion"],
          unsanctioned: acc.unsanctioned + s["unsanctioned_work_starts"]
        }
    end
  end

  defp wall(records) do
    times = Enum.map(records, & &1["time_ns"])
    Enum.max(times) - Enum.min(times)
  end

  # Where the run's time sits: before the first compiler job, inside the jobs,
  # inside native codegen, and after the last span (the program itself runs
  # there, with no span of its own).
  defp timeline(records, spans) do
    first = records |> Enum.map(& &1["time_ns"]) |> Enum.min()
    last = records |> Enum.map(& &1["time_ns"]) |> Enum.max()
    jobs = for {_id, %{name: "fz.compiler2.job"} = s} <- spans, do: s
    job_first = jobs |> Enum.map(& &1.start) |> Enum.min(fn -> first end)
    job_last = jobs |> Enum.map(&(&1.start + &1.inclusive)) |> Enum.max(fn -> first end)
    job_sum = jobs |> Enum.map(& &1.inclusive) |> Enum.sum()

    codegen =
      spans
      |> Enum.filter(fn {_id, s} -> s.name in ["fz.compiler2.native_backend.compile", "fz.codegen.compile"] end)
      |> Enum.map(fn {_id, s} -> s.inclusive end)
      |> Enum.max(fn -> 0 end)

    IO.puts("timeline (span times include the stream's own rendering; read them as shape, take magnitudes from a sample of the plain binary)")
    row("before the first job", job_first - first)
    row("first job start to last job stop", job_last - job_first)
    row("  sum of job inclusive time", job_sum)
    row("native codegen span", codegen)
    row("after the last span (program run)", last - last_stop(spans, last))
    IO.puts("")
  end

  defp last_stop(spans, default) do
    spans |> Enum.map(fn {_id, s} -> s.start + s.inclusive end) |> Enum.max(fn -> default end)
  end

  defp by_name(spans, top) do
    IO.puts("span names by inclusive time")
    spans
    |> Map.values()
    |> Enum.group_by(& &1.name)
    |> Enum.map(fn {name, ss} -> {name, length(ss), sum(ss, :inclusive), sum(ss, :self)} end)
    |> Enum.sort_by(fn {_, _, inc, _} -> -inc end)
    |> Enum.take(top)
    |> Enum.map(fn {n, c, inc, self} -> {n, c, fmt_ms(inc), fmt_ms(self)} end)
    |> table(["name", "count", "inclusive ms", "self ms"])
  end

  defp by_kind(jobs, top) do
    IO.puts("compiler jobs by kind")
    jobs
    |> Enum.group_by(fn s -> elem(s.label, 0) end)
    |> Enum.map(fn {kind, ss} -> {kind, length(ss), sum(ss, :inclusive), sum(ss, :self), max_ms(ss)} end)
    |> Enum.sort_by(fn {_, _, _, self, _} -> -self end)
    |> Enum.take(top)
    |> Enum.map(fn {k, c, inc, self, mx} -> {k, c, fmt_ms(inc), fmt_ms(self), fmt_ms(mx)} end)
    |> table(["kind", "count", "inclusive ms", "self ms", "max ms"])
  end

  defp by_subject(jobs, top) do
    IO.puts("compiler jobs by kind and subject")
    jobs
    |> Enum.group_by(& &1.label)
    |> Enum.map(fn {{kind, subject}, ss} -> {"#{kind} #{subject}", length(ss), sum(ss, :inclusive), sum(ss, :self)} end)
    |> Enum.sort_by(fn {_, _, _, self} -> -self end)
    |> Enum.take(top)
    |> Enum.map(fn {k, c, inc, self} -> {k, c, fmt_ms(inc), fmt_ms(self)} end)
    |> table(["kind subject", "runs", "inclusive ms", "self ms"])
  end

  # A job that ran more than once for the same subject was woken by a changed
  # fact; the count says how many climbs the fixpoint took there.
  defp reruns(jobs, top) do
    IO.puts("most re-run jobs")
    jobs
    |> Enum.group_by(& &1.label)
    |> Enum.map(fn {{kind, subject}, ss} -> {"#{kind} #{subject}", length(ss), sum(ss, :self)} end)
    |> Enum.filter(fn {_, n, _} -> n > 1 end)
    |> Enum.sort_by(fn {_, n, self} -> {-n, -self} end)
    |> Enum.take(top)
    |> Enum.map(fn {k, n, self} -> {k, n, fmt_ms(self)} end)
    |> table(["kind subject", "runs", "self ms"])
  end

  defp sum(spans, key), do: spans |> Enum.map(&Map.fetch!(&1, key)) |> Enum.sum()
  defp max_ms(spans), do: spans |> Enum.map(& &1.inclusive) |> Enum.max()

  defp row(label, ns), do: IO.puts("  #{String.pad_trailing(label, 36)} #{String.pad_leading(fmt_ms(ns), 10)} ms")

  defp table(rows, headers) do
    rows = Enum.map(rows, fn r -> r |> Tuple.to_list() |> Enum.map(&cell/1) end)
    widths =
      [headers | rows]
      |> Enum.zip_with(fn col -> col |> Enum.map(&String.length/1) |> Enum.max() end)

    line = fn cells ->
      cells
      |> Enum.zip(widths)
      |> Enum.with_index()
      |> Enum.map(fn {{c, w}, i} -> if i == 0, do: String.pad_trailing(c, w), else: String.pad_leading(c, w) end)
      |> Enum.join("  ")
    end

    IO.puts("  " <> line.(headers))
    Enum.each(rows, &IO.puts("  " <> line.(&1)))
    IO.puts("")
  end

  defp cell(v) when is_integer(v), do: Integer.to_string(v)
  defp cell(nil), do: "-"
  defp cell(v) when is_binary(v), do: String.slice(v, 0, 70)
  defp cell(v), do: inspect(v)

  defp fmt_ms(ns), do: :erlang.float_to_binary(ns / 1_000_000, decimals: 1)
end

Distill.main(System.argv())
