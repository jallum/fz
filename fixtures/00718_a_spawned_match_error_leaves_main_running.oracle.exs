Logger.configure(level: :none)

defmodule Oracle do
  def fetch(), do: Enum.at([{:error, :closed}], 0)
end

parent = self()

spawn(fn ->
  send(parent, :child_started)
  {:ok, value} = Oracle.fetch()
  send(parent, value)
end)

receive do
  message -> IO.inspect(message)
end

IO.inspect(:main_carried_on)
