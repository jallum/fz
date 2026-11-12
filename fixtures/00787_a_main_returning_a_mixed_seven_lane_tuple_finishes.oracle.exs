defmodule Oracle do
  def main() do
    IO.inspect({:a, "s", [1], 4, 5, 6.0, 7})
    {:a, "s", [1], 4, 5, 6.0, 7}
  end
end

Oracle.main()
