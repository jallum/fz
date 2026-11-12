defmodule Oracle do
  def run() do
    IO.inspect(OptionParser.parse(System.argv(), strict: [ratio: :float]))
    IO.inspect(OptionParser.parse(["--ratio", "1e3"], strict: [ratio: :float]))
    IO.inspect(OptionParser.parse(["--ratio", "3"], strict: [ratio: :float]))
    IO.inspect(OptionParser.parse(["--ratio=-0.5"], strict: [ratio: :float]))
    IO.inspect(OptionParser.parse(["--ratio", ".5"], strict: [ratio: :float]))
    IO.inspect(OptionParser.parse(["--ratio", "1."], strict: [ratio: :float]))
    IO.inspect(OptionParser.parse(["--ratio", "2.5kg"], strict: [ratio: :float]))
    IO.inspect(OptionParser.parse(["--ratio", "abc"], strict: [ratio: :float]))
    IO.inspect(OptionParser.parse(["--ratio", "1e400"], strict: [ratio: :float]))
    IO.inspect(OptionParser.parse(["--ratio", "0.1", "--ratio", "0.2"], strict: [ratio: :float]))
  end
end

Oracle.run()
