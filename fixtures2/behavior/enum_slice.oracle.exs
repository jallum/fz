xs = [1, 2, 3, 4, 5]
map = %{"a" => 1, "b" => 2, "c" => 3}

IO.inspect(Enum.slice(xs, 1, 3))
IO.inspect(Enum.slice(xs, 9, 2))
IO.inspect(Enum.slice(xs, -2, 3))
IO.inspect(Enum.slice(xs, -9, 2))
IO.inspect(Enum.slice(xs, 0, 0))
IO.inspect(Enum.slice([], 0, 3))
IO.inspect(Enum.slice(1..10//2, 1, 3))
IO.inspect(Enum.slice(map, 1, 1))

IO.inspect(Enum.slice(xs, 1..3))
IO.inspect(Enum.slice(xs, -3..-1))
IO.inspect(Enum.slice(xs, 0..10//3))
IO.inspect(Enum.slice(xs, 4..2//1))
IO.inspect(Enum.slice(xs, 1..-1//1))
IO.inspect(Enum.slice(1..10, 1..4//2))
IO.inspect(Enum.slice(map, 0..2//2))
