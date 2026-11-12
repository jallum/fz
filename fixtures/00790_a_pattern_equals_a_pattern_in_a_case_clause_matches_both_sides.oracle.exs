defmodule Oracle do
  def classify(s) do
    case s do
      {_id, %{name: "a"} = m} -> {:a, Map.get(m, :v)}
      {_id, m = %{name: "b"}} -> {:b, Map.get(m, :v)}
      {a, _} = {_, b} -> {:other, a, Map.get(b, :name)}
    end
  end

  def run(l) do
    case l do
      [h | _] = [_, x | _] = all -> {h, x, length(all)}
      _ -> :short
    end
  end

  def main() do
    IO.inspect(classify({1, %{name: "a", v: 10}}))
    IO.inspect(classify({2, %{name: "b", v: 20}}))
    IO.inspect(classify({3, %{name: "c", v: 30}}))
    IO.inspect(run([1, 2, 3]))
    IO.inspect(run([1]))
  end
end

Oracle.main()
