defmodule P do
  def either(n, flag) do
    if flag, do: n, else: :none
  end

  def joined(n, flag) do
    value = if flag, do: either(n, flag), else: :none
    value
  end

  def holder(n, flag) do
    value = either(n, flag)
    fn -> value end
  end

  def across(n, flag) do
    first = either(n, flag)
    second = either(n + 1, flag)
    {first, second}
  end

  def steps(i, count) do
    if i == count do
      :done
    else
      flag = rem(i, 2) == 0
      _ = either(i, flag)
      _ = joined(i, flag)
      _ = holder(i, flag).()
      _ = across(i, flag)
      steps(i + 1, count)
    end
  end
end

IO.inspect({P.either(7, true), P.either(7, false)})
IO.inspect({P.joined(7, true), P.joined(7, false)})
IO.inspect({P.holder(7, true).(), P.holder(7, false).()})
IO.inspect({P.across(7, true), P.across(7, false)})
