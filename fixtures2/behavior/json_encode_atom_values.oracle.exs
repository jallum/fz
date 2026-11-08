IO.inspect(JSON.encode!(:foo))
IO.inspect(JSON.encode!([:a, :b]))
IO.inspect(JSON.encode!(%{k: :v}))
IO.inspect(JSON.encode!(:"with space"))
