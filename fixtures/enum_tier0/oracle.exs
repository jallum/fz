xs = [1, 2, 3, 4]
range = 1..7//2
map = %{2 => :two, 1 => :one}

IO.inspect(Enum.reduce(xs, fn x, acc -> x * acc end))
IO.inspect(Enum.reduce(xs, 0, fn x, acc -> acc + x end))
IO.inspect(Enum.reduce_while(xs, 0, fn x, acc ->
  if x < 3 do
    {:cont, acc + x}
  else
    {:halt, acc}
  end
end))
IO.inspect(Enum.each([:a, :b], fn x -> x end))
IO.inspect(Enum.count(range))
IO.inspect(Enum.count(xs, fn x -> x > 2 end))
IO.inspect(Enum.member?(range, 5))
IO.inspect(Enum.member?(range, 6))
IO.inspect(Enum.member?(map, {1, :one}))
IO.inspect(Enum.to_list(range))
IO.inspect(Enum.to_list(map))
IO.inspect(Enum.reverse(xs))
IO.inspect(Enum.reverse(range, [:tail]))
