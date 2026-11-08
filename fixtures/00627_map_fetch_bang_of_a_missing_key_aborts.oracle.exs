try do
  value = hd([2])
  Map.fetch!(%{1 => :a}, value)
  raise "no exception was raised"
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
