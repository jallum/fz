defmodule Oracle do
  def run() do
    IO.inspect([{Foo, 1}])
    IO.inspect([{:a, 1}, {Foo.Bar, 2}])
    IO.inspect([a: 1])
  end
end

Oracle.run()
