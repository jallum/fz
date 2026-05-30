add = &(&1 + &2)
classify = fn
  0 -> :zero
  n when n > 0 -> :pos
  _ -> :other
end

IO.inspect(add.(20, 22))
IO.inspect({classify.(0), classify.(2), classify.(-1)})
