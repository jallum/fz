defmodule Oracle do
  def attempt(f) do
    try do
      try do
        f.()
      catch
        :error, :never -> :never
      end
    rescue
      ArgumentError -> :rescued_by_middle
    catch
      kind, value -> {kind, value}
    end
  end
end

IO.inspect(Oracle.attempt(fn -> throw(:t) end))
IO.inspect(Oracle.attempt(fn -> exit(:x) end))
IO.inspect(Oracle.attempt(fn -> raise ArgumentError, "a" end))
IO.inspect(Oracle.attempt(fn -> :erlang.error(:plain) end))
