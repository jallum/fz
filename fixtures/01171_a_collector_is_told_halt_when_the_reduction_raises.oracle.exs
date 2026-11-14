defmodule Log do
  defstruct [:name]
end

defimpl Collectable, for: Log do
  def into(log) do
    {[], fn acc, cmd ->
      case cmd do
        {:cont, x} -> [x | acc]
        :done -> {log.name, Enum.reverse(acc)}
        :halt ->
          IO.inspect({:halted, acc})
          :ok
      end
    end}
  end
end

defmodule M do
  def explode(3), do: raise(ArgumentError, "three")
  def explode(n), do: n

  def main() do
    IO.inspect(Enum.into([1, 2], %Log{name: :a}))
    r = try do
      Enum.into([1, 2, 3], %Log{name: :b}, &explode/1)
    rescue
      e in ArgumentError -> {:rescued, e.message}
    end
    IO.inspect(r)
    s = try do
      Enum.into(Stream.map([1, 2, 3], fn x -> if x == 3, do: raise(ArgumentError, "three"), else: x end), %Log{name: :s})
    rescue
      e in ArgumentError -> {:rescued_stream, e.message}
    end
    IO.inspect(s)
    t = try do
      Enum.into([1, 2, 3], %Log{name: :c}, fn x -> if x == 2, do: throw(:ball), else: x end)
    catch
      :throw, v -> {:caught, v}
    end
    IO.inspect(t)
    x = try do
      Enum.into([1, 2, 3], %Log{name: :x}, fn x -> if x == 3, do: exit(:stop), else: x end)
    catch
      :exit, reason -> {:exited, reason}
    end
    IO.inspect(x)
    f = try do
      for x <- [1, 2, 3], into: %Log{name: :d}, do: explode(x)
    rescue
      e in ArgumentError -> {:rescued_for, e.message}
    end
    IO.inspect(f)
    IO.inspect(for x <- [1, 2, 3], x != 2, into: %Log{name: :e}, do: x * 10)
  end
end

M.main()
