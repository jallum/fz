defmodule W do
  defexception [:original]
end

defmodule Wrapper do
  def wrap(x) when is_exception(x), do: x
  def wrap(x), do: wrap(%W{original: x})
end

IO.inspect(Wrapper.wrap(:a))
