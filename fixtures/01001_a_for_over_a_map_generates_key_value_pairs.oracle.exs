defmodule Oracle do
  def main() do
    IO.inspect(Enum.sort(for {k, v} <- %{1 => 10, 2 => 20, 3 => 30}, do: k + v))
  end
end

Oracle.main()
