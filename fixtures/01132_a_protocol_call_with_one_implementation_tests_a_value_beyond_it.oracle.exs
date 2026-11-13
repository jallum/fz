defmodule Oracle do
  def join_ints_and_a_tuple() do
    try do
      Enum.join([1, {2, 3}], " ")
    rescue
      e -> Exception.message(e)
    end
  end

  def join_binaries_and_a_tuple() do
    try do
      Enum.join(["x", {1, 2}], " ")
    rescue
      e -> Exception.message(e)
    end
  end

  def main() do
    IO.puts(Enum.join([1, 2, 3], " "))
    IO.puts(Enum.join(["x", "y"], " "))
    IO.puts(join_ints_and_a_tuple())
    IO.puts(join_binaries_and_a_tuple())
  end
end

Oracle.main()
