defmodule Oracle do
  def main() do
    IO.inspect(for {:ok, v} <- [{:ok, 1}, {:error, 2}, {:ok, 3}, :other], do: v * 10)
  end
end

Oracle.main()
