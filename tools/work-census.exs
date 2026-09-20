# Census the work a door does across many programs, ranked by disproportion.
#
# `distill-telemetry.exs` answers "where did this one compilation go". This
# answers the question before it: which programs are the compiler doing too
# much work for, relative to their size. Counts lead, because a job that
# should not have run is a correctness answer; times follow, because once the
# counts are right the remaining juice is how long each job takes.
#
#     elixir tools/work-census.exs run fixtures2/behavior --top 25
#     elixir tools/work-census.exs run fixtures2/behavior --csv census.csv
#
# Columns
#   bytes     the program without its comments -- the input work should track
#   fns       distinct functions the compiler named -- the surface it touched
#   jobs      compiler job spans
#   uniq      distinct (kind, subject) pairs: the jobs that HAD to run at least once
#   rerun%    (jobs - uniq) / jobs -- the share of work that was a repeat
#   j/fn      jobs per function: the proportionality number, small if work
#             tracks the input and large if something is reprocessing
#   hot       runs of the single most re-run (kind, subject)
#   rev       most return-type revisions taken by one activation
#   wall/ms   first record to last
#   jobs/ms   summed job self time

Code.require_file("telemetry.exs", __DIR__)

defmodule WorkCensus do
  def main(args) do
    {opts, [door, target], _} =
      OptionParser.parse(args, strict: [top: :integer, csv: :string, bin: :string, by: :string])

    bin = Keyword.get(opts, :bin, "target/debug/fz2")
    top = Keyword.get(opts, :top, 25)
    by = Keyword.get(opts, :by, "j/fn")

    files = files(target)
    IO.puts("censusing #{length(files)} programs on `#{door}` with #{bin}\n")

    rows =
      files
      |> Enum.map(&measure(&1, door, bin))
      |> Enum.reject(&is_nil/1)

    sorted = Enum.sort_by(rows, &sort_key(&1, by), :desc)

    report(Enum.take(sorted, top))
    totals(rows)
    if csv = Keyword.get(opts, :csv), do: write_csv(csv, Enum.sort_by(rows, & &1.fixture))
  end

  defp files(target) do
    cond do
      File.dir?(target) -> target |> Path.join("**/*.fz") |> Path.wildcard() |> Enum.sort()
      true -> Path.wildcard(target) |> Enum.sort()
    end
  end

  # One program, one trace, one row. A program the door cannot compile is
  # reported rather than skipped silently: a crash is work too, and an
  # unbounded one is the loudest signal there is.
  defp measure(file, door, bin) do
    trace = Path.join(System.tmp_dir!(), "work-census-#{:erlang.phash2(file)}.jsonl")
    File.rm(trace)

    {_out, status} =
      System.cmd(bin, ["--log-telemetry", trace, door, file], stderr_to_stdout: true)

    if not File.exists?(trace) do
      IO.puts("  !! no trace: #{file} (exit #{status})")
      nil
    else
      row = distill(file, trace, status)
      File.rm(trace)
      row
    end
  end

  defp distill(file, trace, status) do
    records = Telemetry.read(trace)
    names = Telemetry.names(records)
    spans = Telemetry.spans(records, names)
    jobs = Telemetry.jobs(spans)

    by_label = Enum.frequencies_by(jobs, & &1.label)
    njobs = length(jobs)
    uniq = map_size(by_label)
    hot = by_label |> Map.values() |> Enum.max(fn -> 0 end)
    fns = map_size(names)

    revisions =
      for %{"name" => ["fz", "compiler2", "return_type", "defined"], "metadata" => %{"activation" => a}} <- records,
          do: Telemetry.subject(a, names)

    %{
      fixture: Path.relative_to_cwd(file),
      bytes: code_bytes(file),
      status: status,
      fns: fns,
      jobs: njobs,
      uniq: uniq,
      reruns: njobs - uniq,
      rerun_pct: if(njobs > 0, do: (njobs - uniq) * 100 / njobs, else: 0.0),
      per_fn: if(fns > 0, do: njobs / fns, else: 0.0),
      hot: hot,
      rev: revisions |> Enum.frequencies() |> Map.values() |> Enum.max(fn -> 0 end),
      wall_ms: Telemetry.wall(records) / 1_000_000,
      jobs_ms: jobs |> Enum.map(& &1.self) |> Enum.sum() |> Kernel./(1_000_000)
    }
  end

  # A fixture carries its paper answer in a leading comment block, so the file's
  # size is prose plus program. Only the program is the input the work should be
  # proportional to.
  defp code_bytes(file) do
    file
    |> File.stream!()
    |> Stream.reject(&(String.trim_leading(&1) |> String.starts_with?("#")))
    |> Enum.map(&byte_size/1)
    |> Enum.sum()
  end

  defp sort_key(r, "j/fn"), do: r.per_fn
  defp sort_key(r, "rerun"), do: r.rerun_pct
  defp sort_key(r, "jobs"), do: r.jobs
  defp sort_key(r, "wall"), do: r.wall_ms
  defp sort_key(r, "hot"), do: r.hot
  defp sort_key(_row, other), do: raise("unknown --by #{other}")

  defp report(rows) do
    header = ~w(fixture bytes fns jobs uniq rerun% j/fn hot rev wall/ms jobs/ms)

    cells =
      Enum.map(rows, fn r ->
        [
          r.fixture,
          Integer.to_string(r.bytes),
          Integer.to_string(r.fns),
          Integer.to_string(r.jobs),
          Integer.to_string(r.uniq),
          :erlang.float_to_binary(r.rerun_pct, decimals: 0),
          :erlang.float_to_binary(r.per_fn, decimals: 1),
          Integer.to_string(r.hot),
          Integer.to_string(r.rev),
          :erlang.float_to_binary(r.wall_ms, decimals: 0),
          :erlang.float_to_binary(r.jobs_ms, decimals: 0)
        ]
      end)

    widths =
      [header | cells]
      |> Enum.zip_with(fn col -> col |> Enum.map(&String.length/1) |> Enum.max() end)

    pad = fn row ->
      row
      |> Enum.zip(widths)
      |> Enum.with_index()
      |> Enum.map(fn {{v, w}, i} -> if i == 0, do: String.pad_trailing(v, w), else: String.pad_leading(v, w) end)
      |> Enum.join("  ")
    end

    IO.puts(pad.(header))
    IO.puts(String.duplicate("-", Enum.sum(widths) + 2 * (length(widths) - 1)))
    Enum.each(cells, &IO.puts(pad.(&1)))
    IO.puts("")
  end

  defp totals(rows) do
    jobs = rows |> Enum.map(& &1.jobs) |> Enum.sum()
    uniq = rows |> Enum.map(& &1.uniq) |> Enum.sum()
    wall = rows |> Enum.map(& &1.wall_ms) |> Enum.sum()
    failed = Enum.count(rows, &(&1.status != 0))

    IO.puts(
      "#{length(rows)} programs: #{jobs} jobs, #{uniq} of them first runs, " <>
        "#{:erlang.float_to_binary((jobs - uniq) * 100 / max(jobs, 1), decimals: 0)}% repeats, " <>
        "#{:erlang.float_to_binary(wall, decimals: 0)} ms total" <>
        if(failed > 0, do: ", #{failed} did not exit 0", else: "")
    )
  end

  # A stable external form, so two censuses can be diffed directly and a
  # prediction can be stated as a file rather than a paragraph.
  defp write_csv(path, rows) do
    lines =
      for r <- rows do
        Enum.join(
          [
            r.fixture,
            r.bytes,
            r.status,
            r.fns,
            r.jobs,
            r.uniq,
            r.hot,
            r.rev,
            Float.round(r.wall_ms, 1),
            Float.round(r.jobs_ms, 1)
          ],
          ","
        )
      end

    File.write!(path, Enum.join(["fixture,bytes,status,fns,jobs,uniq,hot,rev,wall_ms,jobs_ms" | lines], "\n") <> "\n")
    IO.puts("wrote #{path}")
  end
end

WorkCensus.main(System.argv())
