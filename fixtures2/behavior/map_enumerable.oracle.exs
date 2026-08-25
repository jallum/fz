map = %{3 => :three, 1 => :one, 2 => :two}
ints = %{2 => 20, 1 => 10}

IO.inspect(Enumerable.reduce(map, {:cont, []}, fn pair, acc -> {:cont, [pair | acc]} end))
IO.inspect(Enumerable.reduce(ints, {:cont, 0}, fn {_key, value}, acc -> {:cont, acc + value} end))
IO.inspect(Enumerable.reduce(map, {:halt, 99}, fn pair, acc -> {:cont, [pair | acc]} end))

IO.inspect(Enumerable.count(map))
IO.inspect(Enumerable.member?(map, {1, :one}))
IO.inspect(Enumerable.member?(map, {1, :two}))
IO.inspect(Enumerable.member?(map, 1))
{:ok, n, slicer} = Enumerable.slice(map)
IO.inspect(n)
IO.inspect(slicer.(map))
