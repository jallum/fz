defmodule Oracle do
  def run() do
    IO.inspect(OptionParser.parse(System.argv(), strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["-", "f"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["- x", "f"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["a", "--", "b"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--", "--"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["-5", "f"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["-5", "--top", "3"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top", "-"], strict: [top: :string]))
    IO.inspect(OptionParser.parse(["--top", "--", "7"], strict: [top: :integer]))
    IO.inspect(OptionParser.parse(["--top", "-x"], strict: [top: :string]))
    IO.inspect(OptionParser.parse(["--top", "-7"], strict: [top: :string]))
    IO.inspect(OptionParser.parse(["--top", "--7"], strict: [top: :string]))
  end
end

Oracle.run()
