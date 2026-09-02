defmodule Pipeline do
  def apply_twice(f, x), do: f.(f.(x))
end

send(self(), fn n -> n + 1 end)
send(self(), fn n -> n * 3 end)
a = receive do g -> g end
b = receive do g -> g end
IO.inspect(Pipeline.apply_twice(a, 10))
IO.inspect(Pipeline.apply_twice(b, 10))
