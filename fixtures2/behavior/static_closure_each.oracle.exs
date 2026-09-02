double = fn x -> IO.inspect(x * 2) end
Enum.each([1, 2, 3], double)
IO.inspect(:done)
