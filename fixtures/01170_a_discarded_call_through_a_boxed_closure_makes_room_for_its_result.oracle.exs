make = fn map ->
  {map, fn acc, cmd ->
    case cmd do
      :done -> acc
      :halt -> :ok
    end
  end}
end

run = fn map ->
  {initial, collector} = make.(map)
  collector.(initial, :halt)
  collector.(initial, :done)
end

IO.inspect(run.(%{}))
IO.inspect(run.(%{a: 1}))
