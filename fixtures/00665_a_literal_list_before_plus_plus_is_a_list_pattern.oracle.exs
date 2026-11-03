defmodule Oracle do
  def after_header([1, 2] ++ rest), do: {:body, rest}
  def after_header(_), do: :no

  def in_case(list) do
    case list do
      [:a] ++ [:b] ++ rest -> {:ab, rest}
      [:a] ++ rest -> {:a, rest}
      [] ++ rest -> {:any, rest}
    end
  end

  def with_variable(list) do
    case list do
      [x, y] ++ rest -> {x, y, rest}
      _ -> :short
    end
  end

  def exact(list) do
    case list do
      [1] ++ [2] -> :one_two
      _ -> :no
    end
  end

  def in_fn(list) do
    f = fn
      [0] ++ rest -> {:zero, rest}
      _ -> :no
    end

    f.(list)
  end

  def matched(list) do
    [1, 2] ++ rest = list
    rest
  end

  def through_with(list) do
    with [1] ++ rest <- list do
      {:one, rest}
    else
      _ -> :no
    end
  end

  def improper(list) do
    case list do
      [1] ++ rest -> rest
      _ -> :no
    end
  end

  def run() do
    IO.inspect(after_header([1, 2, 3, 4]))
    IO.inspect(after_header([1, 2]))
    IO.inspect(after_header([1]))
    IO.inspect(after_header([2, 1]))
    IO.inspect(after_header("12"))
    IO.inspect(in_case([:a, :b, :c]))
    IO.inspect(in_case([:a, :c]))
    IO.inspect(in_case([:z]))
    IO.inspect(in_case([]))
    IO.inspect(with_variable([1, 2, 3]))
    IO.inspect(with_variable([1]))
    IO.inspect(exact([1, 2]))
    IO.inspect(exact([1, 2, 3]))
    IO.inspect(in_fn([0, :x]))
    IO.inspect(in_fn([1]))
    IO.inspect(matched([1, 2, 3]))
    IO.inspect(through_with([1, 5, 6]))
    IO.inspect(through_with([2]))
    IO.inspect(improper([1, 2]))
  end
end

Oracle.run()
