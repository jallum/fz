IO.inspect(try do
  exit({:stopped, 3})
catch
  :exit, reason -> reason
end)
IO.inspect(try do
  try do
    exit(:inner)
  catch
    thrown -> {:wrong, thrown}
  end
catch
  :exit, reason -> {:outer, reason}
end)
