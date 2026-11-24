defmodule Main do
  defguardp callable?(f) when is_function(f)
  defguardp binary_fn?(f) when is_function(f, 2)
  defguardp positive?(n) when n > 0
  defguardp anything?(_x) when true
  defguardp either?(_x) when true

  def run(g, x) when callable?(g) and binary_fn?(g), do: g.(x, x)
  def run(g, x) when callable?(g), do: g.(x)
  def run(_, _), do: :other

  def sign(n) when positive?(n), do: :pos
  def sign(_), do: :nonpos

  def literal(x) when positive?(3), do: {:three, x}

  def literal_false(x) when positive?(-3), do: {:neg, x}
  def literal_false(x), do: {:not, x}

  def ignored(_x) when anything?(_x), do: :any

  def ambiguous(x) when either?(x) and x > 0, do: :big
  def ambiguous(_), do: :small

  def main() do
    IO.inspect(run(fn a, b -> a + b end, 3))
    IO.inspect(run(fn a -> a * 10 end, 3))
    IO.inspect(run(:atom, 3))
    IO.inspect(sign(5))
    IO.inspect(sign(-5))
    IO.inspect(sign(:nope))
    IO.inspect(literal(1))
    IO.inspect(literal_false(1))
    IO.inspect(ignored(1))
    IO.inspect(ambiguous(7))
    IO.inspect(ambiguous(-7))
    IO.inspect(ambiguous(:a))
  end
end

Main.main()
