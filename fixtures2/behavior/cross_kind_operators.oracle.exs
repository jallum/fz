lt? = fn
  a, b when a < b -> :lt
  _a, _b -> :not_lt
end

le? = fn
  a, b when a <= b -> :le
  _a, _b -> :not_le
end

gt? = fn
  a, b when a > b -> :gt
  _a, _b -> :not_gt
end

ge? = fn
  a, b when a >= b -> :ge
  _a, _b -> :not_ge
end

eq? = fn
  a, b when a == b -> :equal
  _a, _b -> :different
end

# integer vs atom -- body position
IO.inspect(1 < :atom)
IO.inspect(1 <= :atom)
IO.inspect(1 > :atom)
IO.inspect(1 >= :atom)
# integer vs atom -- through a guard
IO.inspect(lt?.(1, :atom))
IO.inspect(le?.(1, :atom))
IO.inspect(gt?.(1, :atom))
IO.inspect(ge?.(1, :atom))

# atom vs binary -- body position
IO.inspect(:atom < "bin")
IO.inspect(:atom <= "bin")
IO.inspect(:atom > "bin")
IO.inspect(:atom >= "bin")
# atom vs binary -- through a guard
IO.inspect(lt?.(:atom, "bin"))
IO.inspect(le?.(:atom, "bin"))
IO.inspect(gt?.(:atom, "bin"))
IO.inspect(ge?.(:atom, "bin"))

# tuple vs binary -- body position
IO.inspect({:foo, 2} < "string")
IO.inspect({:foo, 2} <= "string")
IO.inspect({:foo, 2} > "string")
IO.inspect({:foo, 2} >= "string")
# tuple vs binary -- through a guard
IO.inspect(lt?.({:foo, 2}, "string"))
IO.inspect(le?.({:foo, 2}, "string"))
IO.inspect(gt?.({:foo, 2}, "string"))
IO.inspect(ge?.({:foo, 2}, "string"))

# list vs tuple -- body position
IO.inspect([1, 2] < {1, 2})
IO.inspect([1, 2] <= {1, 2})
IO.inspect([1, 2] > {1, 2})
IO.inspect([1, 2] >= {1, 2})
# list vs tuple -- through a guard
IO.inspect(lt?.([1, 2], {1, 2}))
IO.inspect(le?.([1, 2], {1, 2}))
IO.inspect(gt?.([1, 2], {1, 2}))
IO.inspect(ge?.([1, 2], {1, 2}))

# map vs list -- body position
IO.inspect(%{"a" => 1} < [1])
IO.inspect(%{"a" => 1} <= [1])
IO.inspect(%{"a" => 1} > [1])
IO.inspect(%{"a" => 1} >= [1])
# map vs list -- through a guard
IO.inspect(lt?.(%{"a" => 1}, [1]))
IO.inspect(le?.(%{"a" => 1}, [1]))
IO.inspect(gt?.(%{"a" => 1}, [1]))
IO.inspect(ge?.(%{"a" => 1}, [1]))

# float vs atom -- body position
IO.inspect(1.5 < :atom)
IO.inspect(1.5 <= :atom)
IO.inspect(1.5 > :atom)
IO.inspect(1.5 >= :atom)
# float vs atom -- through a guard
IO.inspect(lt?.(1.5, :atom))
IO.inspect(le?.(1.5, :atom))
IO.inspect(gt?.(1.5, :atom))
IO.inspect(ge?.(1.5, :atom))

# int vs float -- body position
IO.inspect(1 < 1.5)
IO.inspect(1 <= 1.5)
IO.inspect(1 > 1.5)
IO.inspect(1 >= 1.5)
# int vs float -- through a guard
IO.inspect(lt?.(1, 1.5))
IO.inspect(le?.(1, 1.5))
IO.inspect(gt?.(1, 1.5))
IO.inspect(ge?.(1, 1.5))

# float vs int -- body position
IO.inspect(2.0 < 3)
IO.inspect(2.0 <= 3)
IO.inspect(2.0 > 3)
IO.inspect(2.0 >= 3)
# float vs int -- through a guard
IO.inspect(lt?.(2.0, 3))
IO.inspect(le?.(2.0, 3))
IO.inspect(gt?.(2.0, 3))
IO.inspect(ge?.(2.0, 3))

# atom vs atom -- body position
IO.inspect(:a < :b)
IO.inspect(:a <= :b)
IO.inspect(:a > :b)
IO.inspect(:a >= :b)
# atom vs atom -- through a guard
IO.inspect(lt?.(:a, :b))
IO.inspect(le?.(:a, :b))
IO.inspect(gt?.(:a, :b))
IO.inspect(ge?.(:a, :b))

# binary vs binary -- body position
IO.inspect("abc" < "abd")
IO.inspect("abc" <= "abd")
IO.inspect("abc" > "abd")
IO.inspect("abc" >= "abd")
# binary vs binary -- through a guard
IO.inspect(lt?.("abc", "abd"))
IO.inspect(le?.("abc", "abd"))
IO.inspect(gt?.("abc", "abd"))
IO.inspect(ge?.("abc", "abd"))

# tuple vs tuple (arity) -- body position
IO.inspect({1, 2} < {1})
IO.inspect({1, 2} <= {1})
IO.inspect({1, 2} > {1})
IO.inspect({1, 2} >= {1})
# tuple vs tuple (arity) -- through a guard
IO.inspect(lt?.({1, 2}, {1}))
IO.inspect(le?.({1, 2}, {1}))
IO.inspect(gt?.({1, 2}, {1}))
IO.inspect(ge?.({1, 2}, {1}))

# list vs list -- body position
IO.inspect([1, 2, 3] < [2])
IO.inspect([1, 2, 3] <= [2])
IO.inspect([1, 2, 3] > [2])
IO.inspect([1, 2, 3] >= [2])
# list vs list -- through a guard
IO.inspect(lt?.([1, 2, 3], [2]))
IO.inspect(le?.([1, 2, 3], [2]))
IO.inspect(gt?.([1, 2, 3], [2]))
IO.inspect(ge?.([1, 2, 3], [2]))

# int/float equality -- body position
IO.inspect(1 == 1.0)
IO.inspect(1 === 1.0)
IO.inspect(1 != 1.0)
IO.inspect(1 !== 1.0)
# int/float equality -- through a guard
IO.inspect(eq?.(1, 1.0))
IO.inspect(eq?.(1, :atom))
