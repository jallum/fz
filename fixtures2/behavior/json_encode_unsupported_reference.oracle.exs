try do
  JSON.encode!(make_ref())
  raise "no exception was raised"
rescue
  e ->
    [first | _] = String.split(Exception.format_banner(:error, e, __STACKTRACE__), "\n")
    IO.puts(first)
end
