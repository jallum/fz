needle = 7
zero = fn -> :ok end
add = fn x, y -> x + y end
smaller = fn x, y when x < y -> x end
parenthesized = fn (x, y) -> x + y end
unpack = fn {x, y}, [z | zs] -> {x, y, z, zs} end
pinned = fn ^needle, value -> value end

IO.inspect({
  zero.(),
  add.(20, 22),
  smaller.(3, 5),
  parenthesized.(20, 22),
  unpack.({1, 2}, [3, 4, 5]),
  pinned.(7, :pinned)
})
