defmodule M do
  @spec count([a]) :: integer when a: any
  def count([]), do: 0
  def count([_ | t]), do: 1 + count(t)

  @spec count_bounded([a]) :: integer when a: any
  def count_bounded([]), do: 0
  def count_bounded([_ | t]), do: 1 + count_bounded(t)
end

defmodule Main do
  def main() do
    IO.inspect(M.count([fn -> 1 end, 5]))
    IO.inspect(M.count([fn -> 1 end, fn x -> x end, &M.count/1]))
    IO.inspect(M.count([1, 2]))
    IO.inspect(M.count_bounded([fn -> 1 end, 5]))
  end
end

Main.main()
