defmodule Defaults do
  defmacro pair() do
    quote do
      def a(), do: 1
      def b(), do: 2
    end
  end

  defmacro nested() do
    inner =
      quote do
        def c(), do: 3
        def d(), do: 4
      end

    quote do
      unquote(inner)
      def e(), do: c() + d()
    end
  end

  defmacro nothing() do
    quote do
    end
  end
end

defmodule Uses do
  import Defaults
  pair()
  nested()
  nothing()
  def sum(), do: a() + b() + e()
end

defmodule Oracle do
  def run() do
    IO.inspect(Uses.a())
    IO.inspect(Uses.b())
    IO.inspect(Uses.e())
    IO.inspect(Uses.sum())
  end
end

Oracle.run()
