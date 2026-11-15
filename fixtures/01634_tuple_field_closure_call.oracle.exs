defmodule TupleFieldClosureCall do
  def make_adder(c), do: fn n -> n + c end

  def pair_adder(n), do: {fn x -> x + n end, n}
  def call_pair({f, k}), do: f.(k)

  def tag_call({tag, f}, x), do: {tag, f.(x)}

  def pair_const(n), do: {fn _x -> n end, n}

  def pair_two(n, m), do: {fn x -> x + n + m end, n}

  def pair_swapped(n), do: {n, fn x -> x + n end}
  def call_swapped({k, f}), do: f.(k)

  def triple_adder(n), do: {fn x -> x + n end, n, 99}
  def call_triple({f, k, z}), do: f.(k) + z

  def pair_pred(n), do: {fn x -> x > n end, n}

  def pair_returning_pair(n), do: {fn x -> {x + n, n} end, n}

  def call_returning_pair({f, k}) do
    {a, b} = f.(k)
    a + b
  end

  def pair_capture_free(), do: {fn x -> x + 1 end, 5}

  def pair_widened(n), do: {fn x -> if x > 0, do: x + n, else: x * 1.0 end, n}

  def pair_escaping(n), do: {fn x -> x + n end, n}

  def call_and_hold(t) do
    {f, k} = t
    a = f.(k)
    [held | _] = [t]
    {_hf, hn} = held
    a + hn
  end

  def call_and_keep(t) do
    {f, k} = t
    {f.(k), t}
  end
end

alias TupleFieldClosureCall, as: T

IO.inspect(T.call_pair(T.pair_adder(5)))
IO.inspect(T.tag_call({:a, T.make_adder(1)}, 10))
IO.inspect(T.call_pair(T.pair_const(5)))
IO.inspect(T.call_pair(T.pair_two(5, 100)))
IO.inspect(T.call_swapped(T.pair_swapped(5)))
IO.inspect(T.call_triple(T.triple_adder(5)))
IO.inspect(T.call_pair(T.pair_pred(5)))
IO.inspect(T.call_returning_pair(T.pair_returning_pair(5)))
IO.inspect(T.call_pair(T.pair_capture_free()))
IO.inspect(T.call_pair(T.pair_widened(5)))
IO.inspect(T.call_and_hold(T.pair_escaping(5)))
{kept_result, kept} = T.call_and_keep(T.pair_escaping(5))
IO.inspect(kept_result)
{_f, kept_n} = kept
IO.inspect(kept_n)
