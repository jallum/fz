walk = fn
  walk, <<_c, rest :: binary>>, n -> walk.(walk, rest, n + 1)
  _walk, _b, n -> n
end

first_byte = fn
  <<c, _rest :: binary>> -> c
  _b -> :no_match
end

prefixed = fn
  <<"aaa", rest :: binary>> -> {:prefixed, walk.(walk, rest, 0)}
  _b -> :no_match
end

small = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
big = small <> small <> small

IO.inspect(first_byte.(small))
IO.inspect(first_byte.(big))

IO.inspect(prefixed.(small))
IO.inspect(prefixed.(big))

IO.inspect(walk.(walk, small, 0))
IO.inspect(walk.(walk, big, 0))
IO.inspect(walk.(walk, big <> big, 0))
