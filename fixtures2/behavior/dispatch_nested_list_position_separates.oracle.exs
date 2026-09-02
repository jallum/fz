defmodule Nested do
  def kind({:a, xs}) when is_list(xs) do
    if Enum.all?(xs, &is_integer/1), do: 1, else: 2
  end

  def dnik({:a, xs}) when is_list(xs) do
    if Enum.all?(xs, &is_integer/1), do: 1, else: 2
  end

  def axis({:a, xs}) when is_list(xs), do: 1
  def axis({:a, n}) when is_integer(n), do: 2

  def sixa({:a, n}) when is_integer(n), do: 2
  def sixa({:a, xs}) when is_list(xs), do: 1

  def size({:a, []}), do: 1
  def size({:a, xs}) when is_list(xs), do: 2

  def deep({:a, {:b, xs}}) when is_list(xs) do
    if Enum.all?(xs, &is_integer/1), do: 1, else: 2
  end

  def peed({:a, {:b, xs}}) when is_list(xs) do
    if Enum.all?(xs, &is_integer/1), do: 1, else: 2
  end

  def twin({xs, _}) when is_list(xs) do
    if Enum.all?(xs, &is_integer/1), do: 1, else: 2
  end

  def niwt({xs, _}) when is_list(xs) do
    if Enum.all?(xs, &is_integer/1), do: 1, else: 2
  end

  def pick_twin(n) do
    if n > 0 do
      {[n, n], [:ok, :err]}
    else
      {[:ok, :err], [n, n]}
    end
  end

  def pick_head(n) do
    if n > 0 do
      {:a, [n, n]}
    else
      {:a, [:ok, :err]}
    end
  end

  def pick_axis(n) do
    if n > 0 do
      {:a, [n, n]}
    else
      {:a, n}
    end
  end

  def pick_size(n) do
    if n > 0 do
      {:a, []}
    else
      {:a, [n]}
    end
  end

  def pick_deep(n) do
    if n > 0 do
      {:a, {:b, [n, n]}}
    else
      {:a, {:b, [:ok, :err]}}
    end
  end
end

IO.inspect(Nested.kind(Nested.pick_head(1)))
IO.inspect(Nested.kind(Nested.pick_head(0)))
IO.inspect(Nested.dnik(Nested.pick_head(1)))
IO.inspect(Nested.dnik(Nested.pick_head(0)))

IO.inspect(Nested.axis(Nested.pick_axis(1)))
IO.inspect(Nested.axis(Nested.pick_axis(0)))
IO.inspect(Nested.sixa(Nested.pick_axis(1)))
IO.inspect(Nested.sixa(Nested.pick_axis(0)))

IO.inspect(Nested.size(Nested.pick_size(1)))
IO.inspect(Nested.size(Nested.pick_size(0)))

IO.inspect(Nested.deep(Nested.pick_deep(1)))
IO.inspect(Nested.deep(Nested.pick_deep(0)))
IO.inspect(Nested.peed(Nested.pick_deep(1)))
IO.inspect(Nested.peed(Nested.pick_deep(0)))

IO.inspect(Nested.twin(Nested.pick_twin(1)))
IO.inspect(Nested.twin(Nested.pick_twin(0)))
IO.inspect(Nested.niwt(Nested.pick_twin(1)))
IO.inspect(Nested.niwt(Nested.pick_twin(0)))
