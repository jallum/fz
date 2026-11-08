try do
  value = hd([:b])
  Keyword.fetch!([], value)
  raise "no exception was raised"
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
