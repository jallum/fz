defmodule Oracle do
  def main() do
    IO.inspect(inspect(%{"name" => 1, "fz.compiler2.job" => 2, "kind" => 3, "span_id" => 4, "parent" => 5, "duration" => 6, "ts" => 7, "x" => 8}, limit: 6))
    IO.inspect(inspect(%{"name" => "x", "kind" => "job"}, limit: 6))
  end
end

Oracle.main()
