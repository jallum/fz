send(self(), fn x, acc -> acc + x end)
sum = receive do f -> f end
IO.inspect(Enum.reduce([1, 2, 3], 0, sum))
IO.inspect(Enum.reduce([], 7, sum))

send(self(), fn x, acc -> [x | acc] end)
prepend = receive do f -> f end
IO.inspect(Enum.reduce([1, 2, 3], [], prepend))

scale = 10
send(self(), fn x, acc -> acc + x * scale end)
scaled = receive do f -> f end
IO.inspect(Enum.reduce([1, 2, 3], 0, scaled))
