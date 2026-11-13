le = fn ({a, _}, {b, _}) -> a <= b end
lt = fn ({a, _}, {b, _}) -> a < b end
key = fn {k, _} -> k end
inputs = fn n ->
  [
    Enum.map(1..n, fn i -> {div(i, 3), i} end),
    Enum.map(1..n, fn i -> {div(n - i, 3), i} end),
    Enum.map(1..n, fn i -> {rem(i * 7, 4), i} end)
  ]
end
show = fn list -> IO.puts(Enum.map_join(list, " ", fn {k, t} -> "#{k}:#{t}" end)) end
report = fn list ->
  show.(Enum.sort(list, le))
  show.(Enum.sort(list, lt))
  show.(Enum.sort_by(list, key))
end
Enum.each([2, 3, 5, 8, 33], fn n -> Enum.each(inputs.(n), report) end)
report.([{-1, "A"}, {-1, "B"}, {-1, "C"}, {-1, "D"}, {-1, "E"}, {-1, "F"}, {-3, "S"}, {-1, "X"}])
