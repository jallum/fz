reduce_plain = fn
  [], acc, _reducer, _self -> acc
  [head | tail], acc, reducer, self -> self.(tail, reducer.(head, acc), reducer, self)
end

make_reducer = fn predicate ->
  fn entry, acc -> if predicate.(entry), do: acc + 1, else: acc end
end

xs = [1, 2, 3, 4]
IO.inspect(
  reduce_plain.(xs, 0, make_reducer.(fn x -> x > 2 end), reduce_plain) +
    reduce_plain.(xs, 0, make_reducer.(fn x -> rem(x, 2) == 0 end), reduce_plain)
)
