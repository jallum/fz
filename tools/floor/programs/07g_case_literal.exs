# case a do "true" -> .. "false" -> .. end
defmodule Main do
  def loop(0, _a, s), do: s
  def loop(n, a, s) do
    k =
      case a do
        "true" -> 1
        "false" -> 2
        _ -> 0
      end

    loop(n - 1, a, s + k)
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    a = :binary.copy("t", 1) <> "rue"
    IO.inspect(loop(n, a, 0))
  end
end

Main.main()
