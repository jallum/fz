lt? = fn left, right -> left < right end

IO.inspect(lt?.(1, :atom))
IO.inspect(lt?.(:atom, "bin"))
IO.inspect(lt?.("bin", :atom))
IO.inspect(Enum.sort([[1], {1}, :a, "s", 3]))

IO.inspect(Enum.sort([3, 2.5, 1, 2]))

IO.inspect(Enum.sort([:b, :a, :Zed]))

IO.inspect(Enum.sort([{2}, {1, 1}, {1}]))
IO.inspect(lt?.({1, 2}, {1, 2, 3}))
IO.inspect(lt?.({2}, {1, 2}))

IO.inspect(Enum.sort([[2], [1, 1], [1]]))
IO.inspect(lt?.([1, 2, 3], [2]))
IO.inspect(lt?.([1, 2], [1, 2, 3]))

IO.inspect(Enum.sort([%{"b" => 1}, %{"a" => 1}, %{"a" => 0}]))
IO.inspect(lt?.(%{"a" => 1}, %{"b" => 0}))

IO.inspect(Enum.sort(["b", "a", "ab", "", "aa"]))
