result = try do
  IO.inspect(:body)
  :body_value
after
  IO.inspect(:after)
  :after_value
end
IO.inspect(result)
