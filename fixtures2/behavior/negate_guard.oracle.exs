classify = fn x ->
  cond do
    is_float(x) and -x > 0.0 -> :negative_float
    is_integer(x) and -x > 0 -> :negative_int
    true -> :other
  end
end

pick = fn
  0 -> -4.5
  _ -> -9
end

IO.inspect(classify.(-5.5))
IO.inspect(classify.(5.5))
IO.inspect(classify.(-5))
IO.inspect(classify.(5))
IO.inspect(classify.(pick.(0)))
IO.inspect(classify.(pick.(1)))
