defmodule Oracle do
  def main() do
    IO.inspect(inspect(<<1, 2, 3>>, limit: 2))
    IO.inspect(inspect(<<1, 2, 3>>, limit: 3))
    IO.inspect(inspect(<<1, 2, 3::4>>))
    IO.inspect(inspect(<<1, 2, 3::4>>, limit: 2))
    IO.inspect(inspect(<<1, 2, 3::4>>, limit: 0))
    IO.inspect(inspect(<<>>))
    IO.inspect(inspect(<<0>>))
    IO.inspect(inspect(<<255, 254>>, limit: 1))
    IO.inspect(inspect("abcdef", limit: 1))
    IO.inspect(inspect(["abcdef", "ghi"], limit: 1))
  end
end

Oracle.main()
