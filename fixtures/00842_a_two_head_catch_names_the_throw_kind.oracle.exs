defmodule Oracle do
  def find(items) do
    case items do
      [] -> :none
      [first | _] -> throw({:first, first})
    end
  end
end

result = try do
  Oracle.find([7, 8])
catch
  :throw, {:first, value} -> value
end
IO.inspect(result)
