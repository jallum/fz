try do
  map = hd([:first])
  Map.update!(map, 1, fn v -> v end)
  raise "no exception was raised"
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
