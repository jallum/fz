defmodule DefinitionAliases do
  @spec public(integer) :: integer
  def public(value), do: private(value)

  defp private(value), do: value + 1
end

IO.inspect(DefinitionAliases.public(41))
