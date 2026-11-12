defmodule Oracle do
  def main() do
    IO.inspect(inspect(1))
    IO.inspect(inspect(-42))
    IO.inspect(inspect(1.5))
    IO.inspect(inspect("text"))
    IO.inspect(inspect("quote\"d \\ line\n tab\t"))
    IO.inspect(inspect(nil))
    IO.inspect(inspect(true))
    IO.inspect(inspect(false))
    IO.inspect(inspect([]))
    IO.inspect(inspect(%{}))
    IO.inspect(inspect([1, 2, 3]))
    IO.inspect(inspect(["a", "b"]))
    IO.inspect(inspect(%{"k" => "v", "n" => 1}))
    IO.inspect(inspect(%{"outer" => %{"inner" => [1, nil, true]}}))
    IO.inspect(inspect({1, "two", :three}))
    IO.inspect(inspect(inspect("nested")))
  end
end

Oracle.main()
