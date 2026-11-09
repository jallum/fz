defmodule Point do
  defstruct [:x]
end

defmodule Oracle do
  def tuple_field({a, _}) when is_integer(a), do: {:int, a}
  def tuple_field(_), do: :other

  def nested({a, {b, _}}) when is_integer(a) and is_binary(b), do: {:both, a, b}
  def nested(_), do: :other

  def list_head([h | _]) when is_atom(h), do: {:atom, h}
  def list_head(_), do: :other

  def struct_field(%Point{x: x}) when is_integer(x), do: {:point, x}
  def struct_field(_), do: :other

  def case_arm(v) do
    case v do
      n when is_integer(n) -> {:int, n}
      s when is_binary(s) -> {:binary, s}
      _ -> :other
    end
  end

  def case_tuple(v) do
    case v do
      {a, b} when is_integer(a) and is_integer(b) -> a + b
      {a, _} when is_atom(a) -> a
      _ -> :other
    end
  end

  def doubled(n) when is_integer(n) and is_integer(n), do: {:int, n}
  def doubled(_), do: :other

  def partial(m) when is_map(m) and map_size(m) == 0, do: :empty
  def partial(m) when is_map(m), do: :map
  def partial(_), do: :other

  def either(x) when is_integer(x) or is_binary(x), do: :either
  def either(_), do: :neither

  def negated(x) when not is_integer(x), do: :not_int
  def negated(_), do: :int

  def qualified(n) when Kernel.is_integer(n), do: {:int, n}
  def qualified(_), do: :other

  def booleans(b) when is_boolean(b), do: {:boolean, b}
  def booleans(_), do: :other

  def nils(x) when is_nil(x), do: :nothing
  def nils(_), do: :other

  def run do
    IO.inspect([tuple_field({1, :a}), tuple_field({:a, 1}), tuple_field({1.5, 2}), tuple_field(7), tuple_field({1})])
    IO.inspect([nested({1, {"x", :a}}), nested({1, {2, :a}}), nested({"x", {"y", :a}}), nested({1, 2})])
    IO.inspect([list_head([:a, 1]), list_head([1, :a]), list_head([]), list_head(:a)])
    IO.inspect([struct_field(%Point{x: 3}), struct_field(%Point{x: "x"}), struct_field(3)])
    IO.inspect([case_arm(1), case_arm("x"), case_arm(:a), case_arm(1.5)])
    IO.inspect([case_tuple({1, 2}), case_tuple({:a, 2}), case_tuple({1, :a}), case_tuple({"x", "y"}), case_tuple(5)])
    IO.inspect([doubled(4), doubled("x"), doubled(nil)])
    IO.inspect([partial(%{}), partial(%{a: 1}), partial([]), partial(1)])
    IO.inspect([either(1), either("x"), either(:a), either(nil)])
    IO.inspect([negated(1), negated("x"), negated(nil)])
    IO.inspect([qualified(1), qualified("x"), qualified(nil)])
    IO.inspect([booleans(true), booleans(false), booleans(nil), booleans(0)])
    IO.inspect([nils(nil), nils(false), nils(0)])
  end
end

Oracle.run()
