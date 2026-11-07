defmodule Oracle do
  def run() do
    IO.inspect([RuntimeError, Foo.Bar])
    IO.inspect(%{"m" => Foo, Foo.Bar => 1})
    f = fn -> Foo.Bar end
    IO.inspect(f.())
    g = fn m -> m == Foo.Bar end
    IO.inspect(g.(Foo.Bar))
  end
end

Oracle.run()
