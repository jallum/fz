by_alias = try do
  :erlang.error(:boom)
rescue
  e in ErlangError -> e.original
end
IO.inspect(by_alias)
bare = try do
  :erlang.error({:stop, 3})
rescue
  e -> {e.__struct__, e.original}
end
IO.inspect(bare)
