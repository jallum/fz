defmodule Store do
  def get(_map, key), do: {:store_two, key}
  def get(_map, key, default), do: {:store_three, key, default}

  def tag(x), do: {:store_tag, x}

  def describe(map) do
    {get(map, :a), map[:a]}
  end
end

defmodule Aliased do
  alias Store, as: Access

  def through_alias(m), do: {Access.get(m, :a), Access.tag(1)}
end

defmodule M do
  def go do
    m = %{a: 1, b: 2}
    IO.inspect({m[:a], m[:b], m[:missing]})

    IO.inspect({Store.get(m, :a), Store.get(m, :missing)})
    IO.inspect(Aliased.through_alias(m))
    capture = &Store.get/2
    IO.inspect(capture.(m, :captured))
    IO.inspect({Store.get(m, :a, :fallback), Store.get(m, :missing, :fallback)})

    IO.inspect(Store.describe(m))
  end
end

M.go()
