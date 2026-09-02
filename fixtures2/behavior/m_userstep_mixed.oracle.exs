apply_discarding = fn f, x ->
  f.(x)
  :ok
end

double = fn x -> IO.inspect(x * 2) end
IO.inspect(apply_discarding.(double, 1))

send(self(), double)
boxed = receive do f -> f end
IO.inspect(apply_discarding.(boxed, 2))
IO.inspect(:done)
