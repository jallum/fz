# round trip of a 5002-byte binary to another process
defmodule Main do
  def child() do
    receive do
      {from, b} ->
        send(from, byte_size(b))
        child()
    end
  end

  def loop(0, _c, _b, s), do: s
  def loop(n, c, b, s) do
    send(c, {self(), b})

    r =
      receive do
        x -> x
      end

    loop(n - 1, c, b, s + r)
  end

  def main() do
    n = String.to_integer(hd(System.argv()))
    b = :binary.copy("x", 5000) <> "yz"
    c = spawn(fn -> child() end)
    IO.inspect(loop(n, c, b, 0))
  end
end

Main.main()
