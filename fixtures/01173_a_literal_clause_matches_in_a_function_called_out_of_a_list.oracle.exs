defmodule M do
  def pick(3), do: :three
  def pick(:c), do: :see
  def pick(n), do: n

  def explode(3), do: raise(ArgumentError, "three")
  def explode(n), do: n

  def call([fun | _], entry), do: fun.(entry)

  def main() do
    IO.inspect(call([&M.pick/1], 3))
    IO.inspect(call([&M.pick/1], 4))
    IO.inspect(call([&M.pick/1], :c))
    IO.inspect(call([fn x ->
      case x do
        3 -> :three
        n -> n
      end
    end], 3))
    IO.inspect(Enum.to_list(Stream.map([1, 2, 3], &M.pick/1)))
    IO.inspect(Enum.take(Stream.map([:a, :b, :c], &M.pick/1), 3))
    raised = try do
      Enum.to_list(Stream.map([1, 2, 3], &M.explode/1))
    rescue
      e in ArgumentError -> {:rescued, e.message}
    end
    IO.inspect(raised)
  end
end

M.main()
