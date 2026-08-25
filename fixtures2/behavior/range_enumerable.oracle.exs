r = 1..10//2
descending = 10..1//-3
empty = 1..10//-1

IO.inspect(Enumerable.reduce(r, {:cont, 0}, fn x, acc -> {:cont, acc + x} end))
IO.inspect(Enumerable.reduce(descending, {:cont, 0}, fn x, acc -> {:cont, acc + x} end))
IO.inspect(Enumerable.reduce(r, {:halt, 99}, fn x, acc -> {:cont, acc + x} end))

IO.inspect(Enumerable.count(r))
IO.inspect(Enumerable.count(descending))
IO.inspect(Enumerable.count(empty))

IO.inspect(Enumerable.member?(r, 5))
IO.inspect(Enumerable.member?(r, 6))
IO.inspect(Enumerable.member?(descending, 4))
IO.inspect(Enumerable.member?(empty, 1))

{:ok, n, slicer} = Enumerable.slice(r)
IO.inspect(n)
IO.inspect(slicer.(1, 2, 1))
IO.inspect(slicer.(1, 2, 2))
