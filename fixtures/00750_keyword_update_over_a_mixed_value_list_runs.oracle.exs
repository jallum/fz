IO.inspect(Keyword.update([a: 1, s: "x"], :a, 1, fn v -> v + 1 end))
