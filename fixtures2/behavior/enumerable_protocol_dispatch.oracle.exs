values = [[9, 8, 7], 1..9//2, %{1 => :one, 2 => :two}]

result = case values do
  [list, range, map] -> {Enumerable.count(list), Enumerable.count(range), Enumerable.count(map)}
  _ -> :bad_shape
end

IO.inspect(result)
