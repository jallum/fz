# a == "true"
# target: eqw_literal
defmodule Main do
  def loop(0, _a, s), do: s
  def loop(n, a, s) do
    loop(n - 1, a, if(a == "true", do: s + 1, else: s))
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    a = :binary.copy("t", 1) <> "rue"
    IO.inspect(loop(n, a, 0))
  end
end

Main.main()
