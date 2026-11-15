defmodule Oracle do
  def missing(key) do
    try do
      raise KeyError, key: key, term: [:held]
    rescue
      e in KeyError -> [e.key, e.term, e.message, Exception.message(e)]
    end
  end

  def all(), do: missing(:wanted)
  def run() do
    Enum.each(all(), fn r -> IO.inspect(r) end)
  end
end

Oracle.run()
