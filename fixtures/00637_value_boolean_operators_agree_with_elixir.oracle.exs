defmodule Oracle do
  def effect(tag), do: IO.inspect(tag)

  def double(x), do: x * 2

  def run() do
    values = [nil, false, true, 0, [], ""]
    booleans = [true, false]

    IO.inspect(Enum.map(values, fn v -> v || :right end))
    IO.inspect(Enum.map(values, fn v -> v && :right end))
    IO.inspect(Enum.map(values, fn v -> !v end))
    IO.inspect(Enum.map(values, fn v -> !!v end))

    IO.inspect(Enum.map(booleans, fn b -> b and :right end))
    IO.inspect(Enum.map(booleans, fn b -> b or :right end))
    IO.inspect(Enum.map(booleans, fn b -> not b end))
    IO.inspect({true and 0, false or [], true and "", false or nil, true or 0, false and 0})

    IO.inspect(Enum.map([-1, 5, 11], fn x -> x > 0 and x < 10 end))
    IO.inspect(Enum.map([-1, 5, 11], fn x -> x < 0 or x > 10 end))
    IO.inspect(Enum.map([-1, 5, 11], fn x -> not (x > 0) end))

    Enum.each([nil, false], fn v -> IO.inspect(v || effect(:or_right)) end)
    Enum.each([0, 1], fn v -> IO.inspect(v || effect(:or_right)) end)
    Enum.each([nil, false], fn v -> IO.inspect(v && effect(:and_right)) end)
    Enum.each([0, 1], fn v -> IO.inspect(v && effect(:and_right)) end)
    Enum.each(booleans, fn b -> IO.inspect(b or effect(:or_right)) end)
    Enum.each(booleans, fn b -> IO.inspect(b and effect(:and_right)) end)
    IO.inspect({true || raise("unreached"), nil && raise("unreached"), false and raise("unreached"), true or raise("unreached")})

    a = 1
    IO.inspect(nil || (true and 3) && 4)
    IO.inspect(!a == true)
    x = nil || 5
    IO.inspect(x)
    IO.inspect(not false && 7)
    IO.inspect(a || 3 |> double())

    m = %{"k" => [1, 2]}
    IO.inspect({m["k"] || [], m["missing"] || []})
  end
end

Oracle.run()
