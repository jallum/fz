# Reading a `fz2 --log-telemetry` stream.
#
# One place understands the record shapes, so every tool that reports on a
# trace agrees about what a job is, what its subject is, and what a function
# is called. Reports live in the tools that require this one.

defmodule Telemetry do
  @doc "Every record in a JSONL trace, in order."
  def read(path), do: path |> File.stream!() |> Stream.map(&JSON.decode!/1) |> Enum.to_list()

  @doc "The compiler names each function once, in a canon event; jobs name it by id."
  def names(records) do
    for %{"name" => ["fz", "compiler2", "canon", "function"], "metadata" => %{"function_id" => id, "canon" => canon}} <- records,
        into: %{},
        do: {id, canon}
  end

  @doc """
  One map per span: name, label (what it was about), start, inclusive and self
  time in nanoseconds. A child's inclusive time comes out of its parent's self
  time, so self says what a span did on its own.
  """
  def spans(records, names) do
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

    Enum.reduce(with_stops, with_stops, fn {_id, span}, acc ->
      case Map.fetch(acc, span.parent) do
        {:ok, parent} -> Map.put(acc, parent.id, %{parent | self: parent.self - span.inclusive})
        :error -> acc
      end
    end)
  end

  @doc "The compiler-job spans, which are the ones carrying a job label."
  def jobs(spans), do: for({_id, %{name: "fz.compiler2.job"} = s} <- spans, do: s)

  @doc "A job's subject, with a function named rather than numbered."
  def subject(job, names) do
    fields = Map.drop(job, ["kind", "opaque_type"])
    name = for {"function_id", id} <- fields, do: Map.get(names, id, "f#{id}")

    rest =
      fields
      |> Map.drop(["function_id"])
      |> Enum.sort_by(fn {k, _} -> k end)
      |> Enum.map(fn {k, v} -> "#{k}=#{inspect(v)}" end)

    Enum.join(name ++ rest, " ")
  end

  @doc "Nanoseconds from the first record to the last."
  def wall(records) do
    times = Enum.map(records, & &1["time_ns"])
    Enum.max(times) - Enum.min(times)
  end

  defp label(%{"job" => job}, names), do: {job["kind"], subject(job, names)}
  defp label(%{} = meta, _names) when map_size(meta) == 0, do: {nil, ""}
  defp label(meta, _names), do: {nil, inspect(meta, limit: 6)}
end
