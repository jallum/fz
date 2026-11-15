defmodule Counter do
  defstruct [:n, :tag]
end

defmodule Oracle do
  def count(c, 0), do: c
  def count(c, k), do: count(%{c | n: c.n + 1}, k - 1)

  def bump(c), do: %{c | n: c.n + 1}

  def bump_first({c}), do: bump(c)

  def run do
    threaded = count(%Counter{n: 0, tag: :threaded}, 3)
    IO.inspect(threaded.n)

    held = count(%Counter{n: 10, tag: :held}, 1)
    IO.inspect(bump(held).n)
    IO.inspect(held.n)

    boxed = {count(%Counter{n: 20, tag: :boxed}, 1)}
    IO.inspect(bump_first(boxed).n)
    IO.inspect(elem(boxed, 0).n)

    captured = count(%Counter{n: 30, tag: :captured}, 1)
    f = fn -> captured end
    IO.inspect(bump(f.()).n)
    IO.inspect(f.().n)

    sent = count(%Counter{n: 40, tag: :sent}, 1)
    me = self()
    pid = spawn(fn -> receive do %Counter{} = c -> send(me, bump(c)) end end)
    send(pid, sent)
    receive do c -> IO.inspect(c.n) end
    IO.inspect(sent.n)

    kept = count(%Counter{n: 50, tag: :kept}, 1)
    garbage = Enum.to_list(1..200000)
    IO.inspect(length(garbage))
    IO.inspect(bump(kept).n)
  end
end

Oracle.run()
