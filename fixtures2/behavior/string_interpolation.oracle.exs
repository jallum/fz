x = 1
name = "ada"

IO.inspect("a#{x}b")
IO.inspect("#{x}")
IO.inspect("no interp")
IO.inspect("sum #{1 + 2} done")
IO.inspect("atom #{:hi}")
IO.inspect("float #{2.5}")
IO.inspect("bool #{true}")
IO.inspect("nil #{nil}")
IO.inspect("binary #{name}")
IO.inspect("two #{x} and #{name}")
IO.inspect("nested call #{Kernel.to_string(x)} ok")
IO.inspect("list #{Kernel.to_string(x)}#{name}")
IO.inspect("escaped \#{x}")
