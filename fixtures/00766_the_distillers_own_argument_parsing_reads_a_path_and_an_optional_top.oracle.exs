defmodule Oracle do
  def run(args) do
    {opts, [path], _} = OptionParser.parse(args, strict: [top: :integer])
    top = Keyword.get(opts, :top, 20)
    IO.inspect({path, top})
    {opts, [path], _} = OptionParser.parse([path], strict: [top: :integer])
    IO.inspect({path, Keyword.get(opts, :top, 20)})
  end
end

Oracle.run(System.argv())
