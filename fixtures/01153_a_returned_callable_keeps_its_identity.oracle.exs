defmodule Hand do
  def id(f), do: f
  def wrap(f), do: {:w, f}
  def wrap_after(f, 0), do: {:w, f}
  def wrap_after(f, n), do: wrap_after(f, n - 1)
end

defmodule Oracle do
  def run() do
    inc = Hand.id(fn x -> x + 1 end)
    up = Hand.id(&String.upcase/1)
    IO.inspect({inc.(1), up.("a")})

    {:w, inc} = Hand.wrap(fn x -> x + 1 end)
    {:w, up} = Hand.wrap(&String.upcase/1)
    IO.inspect({inc.(1), up.("a")})

    {:w, inc} = Hand.wrap_after(fn x -> x + 1 end, 2)
    {:w, up} = Hand.wrap_after(&String.upcase/1, 2)
    IO.inspect({inc.(1), up.("a")})
  end
end

Oracle.run()
