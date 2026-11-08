try do
  value = hd([-1])
  Enum.drop_every([1], value)
  raise "no exception was raised"
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
