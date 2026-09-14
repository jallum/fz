defmodule M do
  def go do
    x = 1
    same = fn ^x -> :same end
    IO.inspect(same.(1))

    IO.inspect(pick(2).(2))

    choose = fn ^x -> :same
                _ -> :other end
    IO.inspect(choose.(1))
    IO.inspect(choose.(9))
  end

  defp pick(x), do: fn ^x -> :same end
end

M.go()
