again = fn kind, reason ->
  try do
    try do
      :erlang.raise(kind, reason, [])
    catch
      caught_kind, caught -> :erlang.raise(caught_kind, caught, __STACKTRACE__)
    end
  catch
    outer_kind, outer -> {outer_kind, outer}
  end
end

IO.inspect(again.(:throw, :ball))
IO.inspect(again.(:exit, :stop))
IO.inspect(again.(:error, :reason))

rescued = try do
  try do
    raise ArgumentError, "worse"
  rescue
    e in ArgumentError -> :erlang.raise(:error, e, __STACKTRACE__)
  end
rescue
  e in ArgumentError -> {:rescued, e.message}
end
IO.inspect(rescued)
