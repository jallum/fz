defmodule Oracle do
  def kind(x) when is_integer(x), do: :integer
  def kind(x) when is_pid(x), do: :pid
  def kind(_x), do: :other
  def isp(p) when is_pid(p), do: :matched
  def isp(_p), do: :refused
  def isr(r) when is_reference(r), do: :matched
  def isr(_r), do: :refused

  def main() do
    me = self()
    send(me, me)
    send(me, make_ref())
    send(me, 1.5)
    send(me, :an_atom)
    send(me, "bin")
    send(me, [1])
    send(me, 7)
    receive do p -> IO.inspect({:pid_as, kind(p), isp(p), isr(p), is_pid(p), is_reference(p)}) end
    receive do r -> IO.inspect({:ref_as, kind(r), isp(r), isr(r), is_pid(r), is_reference(r)}) end
    receive do f -> IO.inspect({:float_as, isp(f), isr(f), is_pid(f), is_reference(f)}) end
    receive do a -> IO.inspect({:atom_as, isp(a), isr(a), is_pid(a), is_reference(a)}) end
    receive do b -> IO.inspect({:binary_as, isp(b), isr(b), is_pid(b), is_reference(b)}) end
    receive do l -> IO.inspect({:list_as, isp(l), isr(l), is_pid(l), is_reference(l)}) end
    receive do i -> IO.inspect({:int_as, isp(i), isr(i), is_pid(i), is_reference(i)}) end
    IO.inspect({self() == 1, make_ref() == 1, self() == make_ref(), self() == self()})
  end
end

Oracle.main()
