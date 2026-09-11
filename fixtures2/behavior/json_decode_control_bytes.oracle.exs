for byte <- 0..31 do
  IO.inspect(JSON.decode(<<34, byte, 34>>))
end

for byte <- 0..31 do
  IO.inspect(JSON.decode(<<123, 34, byte, 34, 58, 49, 125>>))
end

IO.inspect(
  JSON.decode(<<34, 92, 98, 92, 102, 92, 110, 92, 114, 92, 116,
                92, 117, 48, 48, 48, 48, 34>>)
)
