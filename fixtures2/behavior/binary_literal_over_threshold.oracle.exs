walk = fn
  walk, <<_c, rest :: binary>>, n -> walk.(walk, rest, n + 1)
  _walk, _b, n -> n
end

first_byte = fn
  <<c, _rest :: binary>> -> c
  _b -> :no_match
end

IO.inspect(first_byte.("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"))
IO.inspect(first_byte.("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"))
IO.inspect(walk.(walk, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", 0))
IO.inspect(walk.(walk, "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb", 0))
IO.inspect(walk.(walk, "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc", 0))
IO.inspect(walk.(walk, "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd", 0))
