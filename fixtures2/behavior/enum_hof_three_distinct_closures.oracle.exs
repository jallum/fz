xs = [1, 2, 3]

IO.inspect(Enum.drop_while(xs, fn x -> x < 0 end))
IO.inspect(Enum.drop_while(xs, fn x -> x > 0 end))
IO.inspect(Enum.drop_while(xs, fn x -> x < 2 end))
