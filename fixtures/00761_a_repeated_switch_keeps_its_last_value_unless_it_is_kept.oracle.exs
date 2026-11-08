defmodule Oracle do
  def run() do
    IO.inspect(OptionParser.parse(System.argv(), strict: [top: :integer]))
    IO.inspect(OptionParser.parse(System.argv(), strict: [top: [:integer, :keep]]))
    IO.inspect(OptionParser.parse(["--a", "1", "--b", "2", "--a", "3"], strict: [a: :integer, b: :integer]))
    IO.inspect(OptionParser.parse(["--a", "1", "--b", "2", "--a", "3"], strict: [a: [:keep, :integer], b: :integer]))
    IO.inspect(OptionParser.parse(["--a", "x", "--a", "y"], strict: [a: [:string, :keep]]))
    IO.inspect(OptionParser.parse(["--a", "x", "--a", "y"], strict: [a: :string]))
    IO.inspect(OptionParser.parse(["--a", "x", "--a"], strict: [a: [:string, :keep]]))
  end
end

Oracle.run()
