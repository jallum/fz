s = "hi"
IO.inspect(s)
IO.inspect(s)
IO.inspect(s == "hi")

result =
  case s do
    "hi" -> :matched
    _ -> :no_match
  end

IO.inspect(result)
