take = fn bin, n ->
  case bin do
    <<s :: binary-size(n), rest :: binary>> -> {:ok, s, rest}
    _ -> :error
  end
end
head_tail = fn
  <<s :: binary-size(3), rest :: binary>> -> {:ok, s, rest}
  _b -> :error
end
inner = fn
  <<n, s :: binary-size(n), rest :: binary>> -> {:ok, s, rest}
  _b -> :error
end
IO.inspect(take.("hello world", 5))
IO.inspect(take.("hi", 5))
IO.inspect(head_tail.("abcdef"))
IO.inspect(inner.(<<3, 97, 98, 99, 100>>))
