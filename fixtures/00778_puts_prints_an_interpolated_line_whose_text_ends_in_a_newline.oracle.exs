defmodule Oracle do
  def fmt_ms(ms), do: Integer.to_string(div(ms, 1000))

  def run() do
    IO.puts("#{3} records, #{2} spans, #{fmt_ms(18_100_000)} ms from first record to last\n")
    IO.puts("after")
  end
end

Oracle.run()
