try do
  JSON.encode!(%{<<255>> => 1})
  raise "JSON.encode!/1 accepted an invalid UTF-8 object key"
rescue
  error in ErlangError ->
    unless error.original == {:invalid_byte, 255} do
      reraise error, __STACKTRACE__
    end
end
