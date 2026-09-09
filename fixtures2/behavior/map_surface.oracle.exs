m = %{"b" => 2, "a" => 1, "c" => 3}

IO.inspect(map_size(m))
IO.inspect(Map.keys(m))
IO.inspect(Map.values(m))
IO.inspect(Map.to_list(m))

IO.inspect(Map.has_key?(m, "a"))
IO.inspect(Map.has_key?(m, "zz"))

IO.inspect(Map.to_list(Map.delete(m, "b")))
IO.inspect(Map.to_list(Map.delete(m, "zz")))
IO.inspect(map_size(Map.delete(m, "a")))

built = "a"
IO.inspect(Map.has_key?(m, built))
IO.inspect(Map.to_list(Map.delete(m, built)))
