defmodule Stamp do
  defmacro who() do
    quote do
      __MODULE__
    end
  end

  defmacro define_fresh() do
    quote do
      def fresh(), do: %__MODULE__{}
    end
  end

  def own(), do: __MODULE__
end

defmodule Outer do
  defmodule Pt do
    import Stamp
    defstruct x: 0, y: 0
    define_fresh()

    def name(), do: __MODULE__
    def via_macro(), do: who()
    def origin(), do: %__MODULE__{}
    def at(x), do: %__MODULE__{x: x}
    def x(%__MODULE__{x: x}), do: x
    def mine?(%__MODULE__{}), do: true
    def mine?(_), do: false
    def named(), do: {__MODULE__, :tag}
    def same?(m), do: m == __MODULE__
    def call(), do: __MODULE__.at(9)

    def kind(v) do
      case v do
        %__MODULE__{x: 0} -> :origin
        %__MODULE__{} -> :point
        _ -> :other
      end
    end
  end
end

defmodule Oracle do
  def run() do
    IO.inspect(Outer.Pt.name())
    IO.inspect(Outer.Pt.via_macro())
    IO.inspect(Stamp.own())
    IO.inspect(Outer.Pt.origin())
    IO.inspect(Outer.Pt.fresh())
    IO.inspect(Outer.Pt.at(3))
    IO.inspect(Outer.Pt.x(Outer.Pt.at(4)))
    IO.inspect(Outer.Pt.mine?(Outer.Pt.origin()))
    IO.inspect(Outer.Pt.mine?(%{x: 1}))
    IO.inspect(Outer.Pt.named())
    IO.inspect(Outer.Pt.same?(Outer.Pt))
    IO.inspect(Outer.Pt.same?(Stamp))
    IO.inspect(Outer.Pt.call())
    IO.inspect(Outer.Pt.kind(Outer.Pt.origin()))
    IO.inspect(Outer.Pt.kind(Outer.Pt.at(2)))
    IO.inspect(Outer.Pt.kind(7))
  end
end

Oracle.run()
IO.inspect(__MODULE__)
