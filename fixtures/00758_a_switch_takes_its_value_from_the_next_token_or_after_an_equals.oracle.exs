defmodule Oracle do
  def run() do
    IO.inspect(OptionParser.parse(System.argv(), strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top=5", "f"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["f", "--top", "5", "g"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top", "-5"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top", "007"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top=+5"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top=5=6"], strict: [top: :string]))
    IO.inspect(OptionParser.parse([], strict: [top: :integer]))
  end
end

Oracle.run()
