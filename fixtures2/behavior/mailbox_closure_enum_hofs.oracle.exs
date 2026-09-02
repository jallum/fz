send(self(), fn x -> x + 1 end)
bump = receive do f -> f end
IO.inspect(Enum.map([1, 2, 3], bump))

send(self(), fn x -> x > 1 end)
big = receive do f -> f end
IO.inspect(Enum.filter([1, 2, 3], big))

IO.inspect(Enum.reduce(Enum.map([1, 2, 3], bump), 0, fn x, acc -> acc + x end))
