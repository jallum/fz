defmodule Oracle do
  def main() do
    me = self()
    r = make_ref()
    r2 = make_ref()
    child = spawn(fn -> nil end)
    m = %{me => :me, r => :r, r2 => :r2, child => :child, 1 => :one}
    IO.inspect({m[me], m[r], m[r2], m[child], m[1], m[2], map_size(m)})
    m = Map.put(m, me, :again)
    m = Map.put(m, r, :r_again)
    IO.inspect({m[me], m[r], map_size(m), Map.has_key?(m, me), Map.has_key?(m, make_ref())})
    send(me, {me, r})
    receive do
      {p, q} -> IO.inspect({m[p], m[q], Map.get(m, p) == :again, Map.delete(m, q) |> map_size()})
    end
    s = MapSet.new([me, r, me, r, r2, 1])
    IO.inspect({MapSet.size(s), MapSet.member?(s, me), MapSet.member?(s, r2), MapSet.member?(s, make_ref()), MapSet.member?(s, 2)})
    s = MapSet.put(s, child)
    s = MapSet.delete(s, r)
    IO.inspect({MapSet.size(s), MapSet.member?(s, child), MapSet.member?(s, r)})
  end
end

Oracle.main()
