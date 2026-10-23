defmodule Greeter do
  def greet(name), do: "hello " <> name
end

defmodule Later do
  def later(n), do: n * 2
end

x = 20
IO.inspect(Greeter.greet("world"))
:ignored
y = x + 1
IO.inspect(y)
IO.inspect(Later.later(y))
if y > 20 do
  IO.inspect(:big)
end
