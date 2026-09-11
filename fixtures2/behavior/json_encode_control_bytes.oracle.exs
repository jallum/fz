controls = for byte <- 0..31, into: <<>>, do: <<byte>>
value = controls <> <<32, 34, 92, 65>>

IO.inspect(JSON.encode!(value))
IO.inspect(JSON.encode!(%{value => value}))
