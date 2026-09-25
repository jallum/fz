# Distill a `fz2 --log-telemetry` JSONL stream into where the time went.
#
# Spans carry timing: a `span_start` record names what began and a `span_stop`
# record carries `elapsed_ns` for the same `span_id`. Spans nest through
# `parent_span_id`, so a span's INCLUSIVE time contains its children and its
# SELF time is what it spent on its own. Both are summed here by span name and,
# for compiler jobs, by job kind and by the function the job served.
#
#     elixir tools/distill-telemetry.exs trace.jsonl [--top 20]

Code.require_file("telemetry.exs", __DIR__)

defmodule Distill do
  def main(args) do
    {opts, [path], _} = OptionParser.parse(args, strict: [top: :integer])
    top = Keyword.get(opts, :top, 20)

    records = Telemetry.read(path)
    names = Telemetry.names(records)
    spans = Telemetry.spans(records, names)
    wall = Telemetry.wall(records)

    IO.puts("#{length(records)} records, #{map_size(spans)} spans, #{fmt_ms(wall)} ms from first record to last\n")
    timeline(records, spans)
    by_name(spans, top)
    jobs = Telemetry.jobs(spans)
    by_kind(jobs, top)
    by_subject(jobs, top)
    reruns(jobs, top)
    return_revisions(records, names, top)
    wakes(records, jobs, names, top)
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
          do: Telemetry.subject(a, names)

    defined =
      for %{"name" => ["fz", "compiler2", "return_type", "defined"], "metadata" => %{"activation" => a}} <- records,
          do: Telemetry.subject(a, names)

    defined
    |> Enum.frequencies()
    |> Enum.sort_by(fn {activation, n} -> {-n, activation} end)
    |> Enum.take(top)
    |> Enum.map(fn {activation, n} -> {activation, n, if(activation in widened, do: "yes", else: "-")} end)
    |> table(["activation", "revisions", "widened"])
  end

  # Why the most re-run jobs ran again: each work_graph.applied record lists
  # the jobs a completion woke and the fact that caused each wake.
  defp wakes(records, jobs, names, top) do
    IO.puts("wake causes of the most re-run jobs")
    hot =
      jobs
      |> Enum.group_by(& &1.label)
      |> Enum.map(fn {label, ss} -> {label, length(ss)} end)
      |> Enum.filter(fn {_, n} -> n > 1 end)
      |> Enum.sort_by(fn {_, n} -> -n end)
      |> Enum.take(div(top, 3))
      |> Map.new()

    causes =
      for %{"name" => ["fz", "compiler2", "work_graph", "applied"], "metadata" => %{"completion" => c}} <- records,
          wake <- c["wakes"] || [],
          key = {wake["job"]["kind"], Telemetry.subject(wake["job"], names)},
          Map.has_key?(hot, key),
          do: {key, cause(wake["cause"], c, names)}

    causes
    |> Enum.group_by(fn {key, _} -> key end, fn {_, cause} -> cause end)
    |> Enum.sort_by(fn {key, _} -> -Map.fetch!(hot, key) end)
    |> Enum.each(fn {{kind, subject}, cs} ->
      IO.puts("  #{kind} #{subject}: #{Map.fetch!(hot, {kind, subject})} runs")
      cs
      |> Enum.frequencies()
      |> Enum.sort_by(fn {_, n} -> -n end)
      |> Enum.take(6)
      |> Enum.each(fn {cause, n} -> IO.puts("    #{String.pad_leading(Integer.to_string(n), 4)}  #{cause}") end)
    end)

    IO.puts("")
  end

  defp cause(cause, completion, names) do
    fact = cause |> Map.drop(["use", "opaque_type"]) |> Telemetry.subject(names)
    from = "#{completion["kind"]} #{completion |> Map.take(["function_id", "arrow", "root_id", "executable"]) |> Telemetry.subject(names)}"
    "#{cause["kind"]} #{fact} (#{cause["use"]}) after #{from}"
  end

  # Where the run's time sits: before the first compiler job, inside the jobs,
  # inside native codegen, and after the last span (the program itself runs
  # there, with no span of its own).
  defp timeline(records, spans) do
    first = records |> Enum.map(& &1["time_ns"]) |> Enum.min()
    last = records |> Enum.map(& &1["time_ns"]) |> Enum.max()
    jobs = Telemetry.jobs(spans)
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
