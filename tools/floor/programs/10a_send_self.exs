# send a 22-byte binary to self and receive it
# target: send_self
defmodule Main do
  def loop(0, _b, s), do: s
  def loop(n, b, s) do
    send(self(), b)

    r =
      receive do
        x -> byte_size(x)
      end

    loop(n - 1, b, s + r)
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    b = :binary.copy("x", 20) <> "yz"
    IO.inspect(loop(n, b, 0))
  end
end

Main.main()
