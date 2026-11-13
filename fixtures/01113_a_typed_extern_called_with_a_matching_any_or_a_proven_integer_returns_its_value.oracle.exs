IO.inspect(2 + 3)
send(self(), 7)

receive do
  x -> IO.inspect(x + 1)
end
