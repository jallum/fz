pick = fn
  0 -> 4.5
  _ -> 9
end

negate_any = fn x -> -x end

IO.inspect(-pick.(0))
IO.inspect(-pick.(1))
IO.inspect(negate_any.(2.5))
IO.inspect(negate_any.(7))
IO.inspect(negate_any.(0.0))
IO.inspect(-0.0)
IO.inspect(-3)
IO.inspect(-3.5)
