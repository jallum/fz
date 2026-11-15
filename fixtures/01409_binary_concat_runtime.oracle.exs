small = "foo" <> "bar"
long_left = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
long = long_left <> "bbbb"

IO.inspect(small)
IO.inspect(long)
IO.inspect(String.valid?(long))
