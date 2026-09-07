IO.inspect(JSON.decode("true"))
IO.inspect(JSON.decode("false"))
IO.inspect(JSON.decode("null"))
IO.inspect(JSON.decode("0"))
IO.inspect(JSON.decode("42"))
IO.inspect(JSON.decode("-45"))
IO.inspect(JSON.decode("3.5"))
IO.inspect(JSON.decode("-0.25"))
IO.inspect(JSON.decode("  \"hi\"  "))
IO.inspect(JSON.decode("[]"))
IO.inspect(JSON.decode("[1, 2.5, true, null]"))
IO.inspect(JSON.decode("[[1], [2, [3]]]"))
IO.inspect(JSON.decode("{}"))
IO.inspect(JSON.decode("{\"a\": 1}"))
IO.inspect(JSON.decode("{\"b\": 2, \"a\": [1, null]}"))
IO.inspect(JSON.decode("{\"n\": {\"m\": {\"deep\": true}}}"))

IO.inspect(JSON.decode("1e3"))
IO.inspect(JSON.decode("1.5e2"))
IO.inspect(JSON.decode("2E+3"))
IO.inspect(JSON.decode("1.0e-7"))
IO.inspect(JSON.decode("-1.5e2"))

IO.inspect(JSON.decode("\"a\\nb\""))
IO.inspect(JSON.decode("\"q\\\"q\""))
IO.inspect(JSON.decode("\"s\\\\s\""))
IO.inspect(JSON.decode("\"sl\\/sl\""))
IO.inspect(JSON.decode("\"\\u0041\""))
IO.inspect(JSON.decode("\"\\u00e9\""))
IO.inspect(JSON.decode("\"\\u65e5\""))

IO.inspect(JSON.encode!(true))
IO.inspect(JSON.encode!(nil))
IO.inspect(JSON.encode!(42))
IO.inspect(JSON.encode!(-45))
IO.inspect(JSON.encode!(2.5))
IO.inspect(JSON.encode!("hi"))
IO.inspect(JSON.encode!([]))
IO.inspect(JSON.encode!([1, 2.5, nil]))
IO.inspect(JSON.encode!(%{}))
IO.inspect(JSON.encode!(%{"a" => [1, nil], "b" => 2}))

ok? = fn r -> match?({:ok, _}, r) end

IO.inspect(ok?.(JSON.decode("[1] junk")))
IO.inspect(ok?.(JSON.decode("[1,]")))
IO.inspect(ok?.(JSON.decode("{\"a\": 1,}")))
IO.inspect(ok?.(JSON.decode("{\"a\" 1}")))
IO.inspect(ok?.(JSON.decode("")))
IO.inspect(ok?.(JSON.decode("tru")))
IO.inspect(ok?.(JSON.decode("[1 2]")))

roundtrip = fn v ->
  case JSON.decode(JSON.encode!(v)) do
    {:ok, decoded} -> decoded == v
    _ -> false
  end
end

IO.inspect(roundtrip.(true))
IO.inspect(roundtrip.(nil))
IO.inspect(roundtrip.(42))
IO.inspect(roundtrip.(-45))
IO.inspect(roundtrip.(2.5))
IO.inspect(roundtrip.("hi"))
IO.inspect(roundtrip.([]))
IO.inspect(roundtrip.([1, 2.5, nil]))
IO.inspect(roundtrip.(%{}))
IO.inspect(roundtrip.(%{"a" => [1, nil], "b" => 2}))
