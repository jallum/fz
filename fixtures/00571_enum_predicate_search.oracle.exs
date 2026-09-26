xs = [1, 2, 3, 4]

IO.inspect(Enum.all?(xs))
IO.inspect(Enum.all?([true, 1, :ok]))
IO.inspect(Enum.all?([true, false]))
IO.inspect(Enum.all?(xs, fn x -> x < 5 end))
IO.inspect(Enum.all?(xs, fn x -> x < 3 end))

IO.inspect(Enum.any?([]))
IO.inspect(Enum.any?([nil, false]))
IO.inspect(Enum.any?([nil, 2]))
IO.inspect(Enum.any?(xs, fn x -> x == 3 end))
IO.inspect(Enum.any?(xs, fn x -> x > 9 end))

IO.inspect(Enum.empty?([]))
IO.inspect(Enum.empty?(xs))

IO.inspect(Enum.find(xs, fn x -> x > 2 end))
IO.inspect(Enum.find(xs, :none, fn x -> x > 2 end))
IO.inspect(Enum.find(xs, :none, fn x -> x > 9 end))

IO.inspect(Enum.find_index(xs, fn x -> rem(x, 2) == 0 end))
IO.inspect(Enum.find_index(xs, fn x -> x > 9 end))

IO.inspect(Enum.find_value(xs, fn x -> if rem(x, 2) == 0, do: {:even, x}, else: false end))
IO.inspect(Enum.find_value(xs, :none, fn x -> if x > 9, do: x, else: nil end))
IO.inspect(Enum.find_value([nil, false, :ok], :none, fn x -> x end))

IO.inspect(Enum.all?([1, 2], fn x -> if x == 1, do: false, else: raise("late all?") end))
IO.inspect(Enum.any?([1, 2], fn x -> if x == 1, do: true, else: raise("late any?") end))
IO.inspect(Enum.find([1, 2], :none, fn x -> if x == 1, do: true, else: raise("late find") end))
IO.inspect(Enum.find_value([1, 2], :none, fn x -> if x == 1, do: :first, else: raise("late find_value") end))
