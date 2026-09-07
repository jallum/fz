IO.inspect(to_string(:hello))
IO.inspect(to_string(nil))
IO.inspect(to_string(:nil_is_not_nil))
IO.inspect(Atom.to_string(nil))

IO.inspect(to_string("already a binary"))
IO.inspect(to_string(""))

IO.inspect(to_string(0))
IO.inspect(to_string(42))
IO.inspect(to_string(-7))

IO.inspect(to_string(2.5))
IO.inspect(to_string(1.0))
IO.inspect(to_string(-0.0))
IO.inspect(to_string(0.1))

IO.inspect(1000000000000000.0)
IO.inspect(to_string(1000000000000000.0))

IO.inspect(to_string(:""))
