by_zero = fn
  x when x / 0 > 0 -> :matched
  _x -> :fell_through
end

rem_by_zero = fn
  x when rem(x, 0) == 0 -> :matched
  _x -> :fell_through
end

float_by_zero = fn
  x when x / 0.0 > 0 -> :matched
  _x -> :fell_through
end

plus_one = fn
  x when x + 1 > 0 -> :matched
  _x -> :fell_through
end

half_is_two = fn
  x when x / 2 == 2 -> :matched
  _x -> :fell_through
end

times_two = fn
  x when x * 2 > 10 -> :matched
  _x -> :fell_through
end

IO.inspect(by_zero.(1))
IO.inspect(rem_by_zero.(7))
IO.inspect(float_by_zero.(1.0))
IO.inspect(plus_one.(:a))
IO.inspect(plus_one.(1))
IO.inspect(plus_one.(-1))
IO.inspect(half_is_two.(5))
IO.inspect(half_is_two.(4))
IO.inspect(times_two.(6))
IO.inspect(times_two.(:a))
