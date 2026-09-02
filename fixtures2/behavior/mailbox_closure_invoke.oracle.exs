send(self(), fn n -> n + 1 end)
send(self(), fn n -> n + 1 end)

receive do
  f -> IO.inspect(f.(10))
end

g = receive do h -> h end
IO.inspect(g.(20))
IO.inspect(g.(30))
