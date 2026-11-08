defmodule Oracle do
  def run() do
    IO.inspect(OptionParser.parse(System.argv(), strict: [verbose: :count], aliases: [v: :verbose]))
    IO.inspect(OptionParser.parse(["--verbose"], strict: [verbose: :count]))
    IO.inspect(OptionParser.parse(["--verbose", "5"], strict: [verbose: :count]))
    IO.inspect(OptionParser.parse(["--verbose=3"], strict: [verbose: :count]))
    IO.inspect(OptionParser.parse(["-vvv"], strict: [verbose: :count], aliases: [v: :verbose]))
    IO.inspect(OptionParser.parse(["--verbose", "--top", "1", "--verbose"], strict: [verbose: :count, top: :integer]))
    IO.inspect(OptionParser.parse(["--top", "1", "--verbose", "--top", "2"], strict: [verbose: :count, top: :integer]))
  end
end

Oracle.run()
