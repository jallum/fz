defmodule Oracle do
  def eval({:num, n}), do: n
  def eval({:add, a, b}), do: eval(a) + eval(b)
  def eval({:mul, a, b}), do: eval(a) * eval(b)
  def eval({:neg, a}), do: 0 - eval(a)

  def run do
    IO.inspect(eval({:num, 42}))
    IO.inspect(eval({:add, {:num, 2}, {:mul, {:num, 3}, {:num, 4}}}))
    tree = {:mul, {:add, {:num, 1}, {:neg, {:num, 2}}}, {:add, {:mul, {:num, 3}, {:num, 4}}, {:neg, {:add, {:num, 5}, {:num, 6}}}}}
    IO.inspect(eval(tree))
    IO.inspect(elem(tree, 1))
  end
end

Oracle.run()
