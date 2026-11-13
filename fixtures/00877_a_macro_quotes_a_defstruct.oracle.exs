defmodule Shapes do
  defmacro point() do
    quote do
      defstruct [:x, :y]
    end
  end

  defmacro tagged(fields) do
    fields = [tag: :shape] ++ fields

    quote do
      defstruct unquote(fields)
    end
  end

  defmacro sized() do
    quote do
      defstruct width: 1, height: 2
    end
  end
end

defmodule Pt do
  import Shapes
  point()
end

defmodule Tagged do
  import Shapes
  tagged([:name, sides: 4])
end

defmodule Sized do
  import Shapes
  sized()
end

defmodule Oracle do
  def run() do
    IO.inspect(%Pt{x: 1, y: 2})
    IO.inspect(%Pt{x: 1})
    IO.inspect(%Tagged{name: "square"})
    IO.inspect(%Tagged{tag: :other, sides: 3})
    IO.inspect(%Sized{})
    IO.inspect(%Sized{height: 5})
  end
end

Oracle.run()
