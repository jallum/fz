try do
  value = hd([2])
  Map.update!(%{1 => :a}, value, fn v -> v end)
  raise "no exception was raised"
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
