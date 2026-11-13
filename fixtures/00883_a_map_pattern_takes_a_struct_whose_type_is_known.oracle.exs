defmodule Pt do
  defstruct x: 1, flag: true
end

defmodule Oracle do
  def x_of(%{x: x}), do: x
  def x_of(_), do: :none

  def module_of(%{__struct__: module}), do: module
  def module_of(_), do: :none

  def flagged(%{flag: true}), do: :yes
  def flagged(_), do: :no

  def flagged_struct(%{__struct__: module, flag: true}) when is_atom(module), do: :yes
  def flagged_struct(_), do: :no

  def run() do
    IO.inspect(x_of(%Pt{}))
    IO.inspect(module_of(%Pt{}))
    IO.inspect(flagged(%Pt{}))
    IO.inspect(flagged(%Pt{flag: false}))
    IO.inspect(flagged_struct(%Pt{}))
    IO.inspect(flagged_struct(:atom))
    IO.inspect(flagged_struct(Map.new(flag: true)))
  end
end

Oracle.run()
