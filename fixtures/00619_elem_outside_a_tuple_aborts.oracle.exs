try do
  value = hd([9])
  elem({1}, value)
  raise "no exception was raised"
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
