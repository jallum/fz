step = fn x, y -> x + y end
r = fn x, y -> rem(x, y) end
IO.inspect(step.(1, 2))
IO.inspect(r.(7, 2))
