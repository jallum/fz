defmodule Oracle do
  def attempt(f) do
    try do
      try do
        f.()
      rescue
        e -> {:rescued, e}
      end
    catch
      kind, value -> {kind, value}
    end
  end
end

IO.inspect(Oracle.attempt(fn -> throw(:ball) end))
IO.inspect(Oracle.attempt(fn -> exit(:leaving) end))
IO.inspect(Oracle.attempt(fn -> raise "oops" end) |> elem(0))
