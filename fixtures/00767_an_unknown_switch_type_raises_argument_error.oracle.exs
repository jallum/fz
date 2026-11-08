try do
  OptionParser.parse(["--top", "5"], strict: [top: :bogus])
  raise "no exception was raised"
rescue
  e -> IO.puts(Exception.format_banner(:error, e, __STACKTRACE__))
end
