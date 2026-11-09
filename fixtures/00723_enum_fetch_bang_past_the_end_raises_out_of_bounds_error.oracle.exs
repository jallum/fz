try do
  value = hd([5])
  Enum.fetch!([1, 2], value)
  raise "no exception was raised"
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
