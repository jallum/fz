defmodule Oracle do
  def run() do
    IO.inspect(OptionParser.parse(System.argv(), strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top="], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top=x"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top", "5x"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top", "1.5"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top", ""], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top", "x", "--top", "5"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--other", "f"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--other", "x", "f"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--other=3", "f"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top", "x", "--other"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--max_top", "3"], strict: [max_top: :integer]))
    IO.inspect(OptionParser.parse(["--top", "99999999999"], strict: [top: :integer]))
  end
end

Oracle.run()
