try do
  JSON.encode!(fn -> 1 end)
  raise "no exception was raised"
rescue
  e ->
    [first | _] = String.split(Exception.format_banner(:error, e, __STACKTRACE__), "\n")
    IO.puts(first)
end
