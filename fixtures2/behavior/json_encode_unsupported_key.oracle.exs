try do
  key = {:tuple, 1}
  JSON.encode!(%{key => "x"})
  raise "no exception was raised"
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
