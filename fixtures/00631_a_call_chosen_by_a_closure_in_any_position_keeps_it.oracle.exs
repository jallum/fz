defmodule Oracle do
  defp second(_x, f), do: f.()
  defp third(_x, _y, f), do: f.()

  def pick_second(f), do: second(0, f)
  def pick_third(f), do: third(0, 1, f)

  def run() do
    IO.inspect([pick_second(fn -> 0 end), pick_second(fn -> 1 end)])
    IO.inspect([pick_third(fn -> 2 end), pick_third(fn -> 3 end)])
  end
end

Oracle.run()
