defmodule Oracle do
  def run() do
    IO.inspect(OptionParser.parse(System.argv(), strict: [verbose: :boolean]))
    IO.inspect(OptionParser.parse(["--no-verbose", "f"], strict: [verbose: :boolean]))
    IO.inspect(OptionParser.parse(["--verbose=true"], strict: [verbose: :boolean]))
    IO.inspect(OptionParser.parse(["--verbose=false"], strict: [verbose: :boolean]))
    IO.inspect(OptionParser.parse(["--verbose=x"], strict: [verbose: :boolean]))
    IO.inspect(OptionParser.parse(["--no-verbose=1"], strict: [verbose: :boolean]))
    IO.inspect(OptionParser.parse(["--no-verbose", "--verbose"], strict: [verbose: :boolean]))
    IO.inspect(OptionParser.parse(["--verbose", "--no-verbose"], strict: [verbose: :boolean]))
    IO.inspect(OptionParser.parse(["--dry-run", "--no-dry-run"], strict: [dry_run: :boolean]))
    IO.inspect(OptionParser.parse(["--no-dry-run"], strict: [dry_run: :boolean]))
    IO.inspect(OptionParser.parse(["--no-other"], strict: [verbose: :boolean]))
    IO.inspect(OptionParser.parse(["--verbose", "--no-verbose"], strict: [verbose: [:boolean, :keep]]))
  end
end

Oracle.run()
