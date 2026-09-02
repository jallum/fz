send(self(), fn x -> IO.inspect(x * 2) end)
double = receive do f -> f end
Enum.each([1, 2, 3], double)

scale = 10
send(self(), fn x -> IO.inspect(x * scale) end)
scaled = receive do f -> f end
Enum.each([4, 5], scaled)

Enum.each([], double)
IO.inspect(:done)
