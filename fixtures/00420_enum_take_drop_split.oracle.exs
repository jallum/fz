xs = [1, 2, 3, 4, 5]
range = 1..5

IO.inspect(Enum.take(xs, 3))
IO.inspect(Enum.take(xs, 0))
IO.inspect(Enum.take(xs, 9))
IO.inspect(Enum.take(xs, -2))
IO.inspect(Enum.take(range, -2))

IO.inspect(Enum.take_while(xs, fn x -> x < 4 end))
IO.inspect(Enum.take_while(xs, fn x -> x < 0 end))
IO.inspect(Enum.take_while(xs, fn x -> x > 0 end))

IO.inspect(Enum.take_every(xs, 0))
IO.inspect(Enum.take_every(xs, 1))
IO.inspect(Enum.take_every(xs, 2))
IO.inspect(Enum.take_every(range, 2))

IO.inspect(Enum.drop(xs, 3))
IO.inspect(Enum.drop(xs, 0))
IO.inspect(Enum.drop(xs, 9))
IO.inspect(Enum.drop(xs, -2))
IO.inspect(Enum.drop(range, -2))

IO.inspect(Enum.drop_while([1, 2, 3, 2, 1], fn x -> x < 3 end))
IO.inspect(Enum.drop_while(xs, fn x -> x < 0 end))
IO.inspect(Enum.drop_while(xs, fn x -> x > 0 end))

IO.inspect(Enum.drop_every(xs, 0))
IO.inspect(Enum.drop_every(xs, 1))
IO.inspect(Enum.drop_every(xs, 2))
IO.inspect(Enum.drop_every(range, 2))

IO.inspect(Enum.split(xs, 3))
IO.inspect(Enum.split(xs, 0))
IO.inspect(Enum.split(xs, 9))
IO.inspect(Enum.split(xs, -2))
IO.inspect(Enum.split(range, -2))

IO.inspect(Enum.split_while(xs, fn x -> x < 4 end))
IO.inspect(Enum.split_while(xs, fn x -> x < 0 end))
IO.inspect(Enum.split_while(xs, fn x -> x > 0 end))

IO.inspect(Enum.split_with(xs, fn x -> rem(x, 2) == 0 end))
IO.inspect(Enum.split_with(xs, fn x -> x < 0 end))
IO.inspect(Enum.split_with(xs, fn x -> x > 0 end))

IO.inspect(Enum.take_while([1, 2, 3], fn x ->
  if x == 1 do
    true
  else
    if x == 2, do: false, else: raise("late take_while")
  end
end))

IO.inspect(Enum.drop_while([1, 2, 3], fn x ->
  if x == 1 do
    true
  else
    if x == 2, do: false, else: raise("late drop_while")
  end
end))

IO.inspect(Enum.split_while([1, 2, 3], fn x ->
  if x == 1 do
    true
  else
    if x == 2, do: false, else: raise("late split_while")
  end
end))
