defmodule Sample do
  defstruct [:step]
end

defmodule Oracle do
  def in_map(n), do: %{step: fn x -> x + n end}

  def in_struct(n), do: %Sample{step: fn x -> x + n end}

  def run do
    m = in_map(1)
    IO.inspect(m.step.(1000))
    s = in_struct(2)
    IO.inspect(s.step.(1000))
    f = s.step
    IO.inspect(f.(1000))
  end
end

Oracle.run()
