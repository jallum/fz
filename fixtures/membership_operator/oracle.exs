xs = [1, 2, 3]
range = 1..7//2
map = %{2 => :two, 1 => :one}

IO.inspect(2 in xs)
IO.inspect(4 in xs)
IO.inspect(5 in range)
IO.inspect(6 not in range)
IO.inspect({1, :one} in map)
IO.inspect({3, :three} not in map)
