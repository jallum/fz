defmodule Oracle do
  def run() do
    IO.inspect(OptionParser.parse(System.argv(), strict: [max_top: :integer]))
    IO.inspect(OptionParser.parse(["--max_top", "3"], strict: [max_top: :integer]))
    IO.inspect(OptionParser.parse(["-t", "5"], strict: [top: :integer], aliases: [t: :top]))
    IO.inspect(OptionParser.parse(["-t5"], strict: [top: :integer], aliases: [t: :top]))
    IO.inspect(OptionParser.parse(["-t=5"], strict: [top: :integer], aliases: [t: :top]))
    IO.inspect(OptionParser.parse(["-t"], strict: [top: :integer], aliases: [t: :top]))
    IO.inspect(OptionParser.parse(["-t", "x"], strict: [top: :integer], aliases: [t: :top]))
    IO.inspect(OptionParser.parse(["-abc", "f"], strict: [alpha: :boolean, beta: :boolean, gamma: :boolean], aliases: [a: :alpha, b: :beta, c: :gamma]))
    IO.inspect(OptionParser.parse(["-ac"], strict: [alpha: :boolean, gamma: :boolean], aliases: [a: :alpha, b: :beta, c: :gamma]))
    IO.inspect(OptionParser.parse(["-at", "5"], strict: [alpha: :boolean, top: :integer], aliases: [a: :alpha, t: :top]))
    IO.inspect(OptionParser.parse(["-at5"], strict: [alpha: :boolean, top: :integer], aliases: [a: :alpha, t: :top]))
    IO.inspect(OptionParser.parse(["-ta", "5"], strict: [alpha: :boolean, top: :integer], aliases: [a: :alpha, t: :top]))
    IO.inspect(OptionParser.parse(["-t", "1", "-t", "2"], strict: [top: [:integer, :keep]], aliases: [t: :top]))
    IO.inspect(OptionParser.parse(["-x", "5"], strict: [top: :integer], aliases: [x: :missing]))
    IO.inspect(OptionParser.parse(["--top", "5"], strict: [top: :integer], aliases: [t: :top]))
  end
end

Oracle.run()
