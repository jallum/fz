try do
  value = hd([-1])
  Enum.map_every([1], value, fn x -> x end)
  raise "no exception was raised"
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
