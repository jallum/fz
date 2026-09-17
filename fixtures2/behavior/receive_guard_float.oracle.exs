send(self(), 2.5)
receive do
  x when x > 1.5 -> IO.inspect(:big)
  x -> IO.inspect({:small, x})
end
