big? = fn n -> n > 10 end
save! = fn n -> n + 1 end
second? = fn a, b -> {a, b} end
IO.inspect({big?.(11), save!.(1)})
value = 4
IO.inspect(save!.(value))
IO.inspect(second?.(1, value))
IO.inspect([ready?: 1, done!: 2, Loud?: 3, Hot!: 4])
IO.inspect({:big?, :save!, :Loud?, :Hot!, :_?})
IO.inspect(Atom.to_string(:a?))
IO.inspect(big?.(1) == false)
