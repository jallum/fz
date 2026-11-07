Logger.configure(level: :none)

defmodule Oracle do
  def zero(0), do: :zero
end

parent = self()

spawn(fn ->
  send(parent, :child_started)
  Oracle.zero(7)
end)

receive do
  message -> IO.inspect(message)
end

IO.inspect(:main_carried_on)
