Logger.configure(level: :none)

parent = self()

spawn(fn ->
  send(parent, :child_started)
  throw(:child_ball)
end)

receive do
  message -> IO.inspect(message)
end

IO.inspect(:main_carried_on)
