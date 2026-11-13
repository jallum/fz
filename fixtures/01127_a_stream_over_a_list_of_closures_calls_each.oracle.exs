IO.inspect(Enum.to_list(Stream.map([fn x -> x end], fn f -> f.(1) end)))
