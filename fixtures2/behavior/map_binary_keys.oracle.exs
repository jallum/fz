built = "a" <> "b"

IO.inspect(%{"ab" => 1, built => 2})
IO.inspect(Enum.count(%{"ab" => 1, built => 2}))

m = %{"ab" => 1, "cd" => 2, "ef" => 3}
IO.inspect(m["ab"])
IO.inspect(m[built])
IO.inspect(m["zz"])

IO.inspect(Enum.to_list(%{"zebra" => 1, "apple" => 2, "mango" => 3}))
IO.inspect(Enum.to_list(%{"aa" => 1, "a" => 2, "ab" => 3}))
