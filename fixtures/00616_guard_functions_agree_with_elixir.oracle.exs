defmodule Oracle do
  def msize(m) when map_size(m) == 0, do: :empty
  def msize(m) when map_size(m) > 0, do: :some
  def msize(_), do: :other

  def tsize(t) when tuple_size(t) == 2, do: :pair
  def tsize(t) when tuple_size(t) > 2, do: :bigger
  def tsize(_), do: :other

  def lsize(l) when length(l) == 3, do: :three
  def lsize(_), do: :other

  def bsize(b) when byte_size(b) == 3, do: :three
  def bsize(_), do: :other

  def nth(t) when elem(t, 1) == :b, do: :b
  def nth(_), do: :other

  def negated(m) when not (map_size(m) == 0), do: :nonempty
  def negated(_), do: :other

  def orred(m) when map_size(m) == 0 or true, do: :yes
  def orred(_), do: :no

  def classify(x) when is_integer(x), do: :integer
  def classify(x) when is_float(x), do: :float
  def classify(x) when is_boolean(x), do: :boolean
  def classify(x) when is_nil(x), do: nil
  def classify(x) when is_atom(x), do: :atom
  def classify(x) when is_binary(x), do: :binary
  def classify(x) when is_list(x), do: :list
  def classify(x) when is_map(x), do: :map
  def classify(x) when is_tuple(x), do: :tuple
  def classify(_), do: :other

  def case_guards(x) do
    case x do
      m when map_size(m) == 0 -> :empty_map
      t when tuple_size(t) == 2 -> :pair
      l when length(l) == 2 -> :two_items
      b when byte_size(b) == 2 -> :two_bytes
      t when elem(t, 0) == :ok -> :ok_tuple
      _ -> :other
    end
  end

  def received(x) do
    send(self(), x)

    receive do
      m when map_size(m) == 0 -> :empty_map
      t when tuple_size(t) == 2 -> :pair
      l when length(l) == 2 -> :two_items
      b when byte_size(b) == 2 -> :two_bytes
      t when elem(t, 0) == :ok -> :ok_tuple
      v when is_integer(v) -> :integer
      v when is_binary(v) -> :binary
      _ -> :other
    end
  end

  def shorted(x) when is_atom(x) or map_size(x) > 0, do: :yes
  def shorted(_), do: :no

  def anded(x) when is_map(x) and map_size(x) == 0, do: :empty
  def anded(_), do: :no

  def received_logic(x) do
    send(self(), x)

    receive do
      v when is_atom(v) or map_size(v) > 0 -> :yes
      v when not (tuple_size(v) == 1) -> :not_one
      _ -> :other
    end
  end

  def run do
    IO.inspect([msize(%{}), msize(%{a: 1}), msize(:x), msize({1}), msize([1])])
    IO.inspect([tsize({1, 2}), tsize({1, 2, 3}), tsize({1}), tsize(:x), tsize(%{})])
    IO.inspect([lsize([1, 2, 3]), lsize([1]), lsize(:x), lsize("abc")])
    IO.inspect([bsize("abc"), bsize("ab"), bsize(:x), bsize([1, 2, 3])])
    IO.inspect([nth({1, :b}), nth({1, :a}), nth({1}), nth(:x), nth([1, :b])])
    IO.inspect([negated(%{a: 1}), negated(%{}), negated(:x)])
    IO.inspect([orred(%{}), orred(%{a: 1}), orred(:x)])

    IO.inspect([classify(1), classify(1.5), classify(true), classify(nil), classify(:a)])
    IO.inspect([classify("bin"), classify([1]), classify(%{a: 1}), classify({1, 2}), classify([])])

    IO.inspect([case_guards(%{}), case_guards({1, 2}), case_guards([1, 2]), case_guards("ab")])
    IO.inspect([case_guards({:ok}), case_guards({:ok, 1, 2}), case_guards(:x), case_guards(7)])

    IO.inspect([received(%{}), received({1, 2}), received([1, 2]), received("ab")])
    IO.inspect([received({:ok}), received({:ok, 1, 2}), received(7), received("abc"), received(:x)])

    IO.inspect([shorted(:a), shorted(%{a: 1}), shorted(%{}), shorted(7)])
    IO.inspect([anded(%{}), anded(%{a: 1}), anded(:x)])
    IO.inspect([received_logic(:a), received_logic(%{a: 1}), received_logic({1}), received_logic({1, 2}), received_logic(7)])
    IO.inspect([case_guards({}), case_guards(%{a: 1}), received({}), received(%{a: 1})])

    IO.inspect([map_size(%{a: 1, b: 2}), tuple_size({1, 2, 3}), length([1, 2, 3]), byte_size("héllo")])
    IO.inspect([elem({1, :b, "c"}, 0), elem({1, :b, "c"}, 2), length([]), tuple_size({})])
    IO.inspect([is_integer(1), is_integer(:a), is_float(1.5), is_boolean(false), is_boolean(:a)])
    IO.inspect([is_nil(nil), is_nil(false), is_atom(nil), is_binary("x"), is_binary(1)])
    IO.inspect([is_list([1]), is_list(:a), is_map(%{}), is_map([]), is_tuple({}), is_tuple([])])
  end
end

Oracle.run()
