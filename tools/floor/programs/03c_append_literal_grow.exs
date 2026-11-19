# acc <> "ab" where acc is the growing result
# n: 10000000 30000000
# target: append
defmodule Main do
  def loop(0, acc), do: acc
  def loop(n, acc), do: loop(n - 1, acc <> "ab")

  def main() do
    n = String.to_integer(hd(System.argv()))
    IO.inspect(byte_size(loop(n, "")))
  end
end

Main.main()
