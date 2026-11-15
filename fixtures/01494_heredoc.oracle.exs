plain = """
hello
"""
IO.inspect(plain)
IO.inspect(byte_size(plain))

nested = """
  indented
    deeper
  """
IO.inspect(nested)

count = 5

interpolated = """
val #{count}
"""
IO.inspect(interpolated)

empty = """
"""
IO.inspect(empty)

escaped = """
a\tb
"""
IO.inspect(escaped)
