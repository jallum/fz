inputs = [
  "\"\\uD83D\\uDE00\"",
  "\"\\uD800\\uDC00\"",
  "\"\\uDBFF\\uDFFF\"",
  "{\"\\uD83D\\uDE00\":1}",
  "\"\\uD7FF\"",
  "\"\\uE000\"",
  "\"\\uD83D\"",
  "\"\\uD83D\\u0041\"",
  "\"\\uD83D\\uD83D\"",
  "\"\\uD83D\\uZZZZ\"",
  "\"\\uD83Dx\"",
  "\"\\uDE00\"",
  "\"x\\uDE00\"",
  "{\"\\uD83D\":1}",
  "{\"\\uDE00\":1}",
  "{\"\\uD83D\\u0041\":1}"
]

for input <- inputs do
  IO.inspect(JSON.decode(input))
end
