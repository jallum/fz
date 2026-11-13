for x <- [0.05, 1.5 / 1_000_000, 2.675, -0.04, 1.0e10, 123_456.789, 2.5, 0.125] do
  for n <- [0, 1, 2, 3] do
    IO.puts(:erlang.float_to_binary(x, decimals: n))
  end
end
