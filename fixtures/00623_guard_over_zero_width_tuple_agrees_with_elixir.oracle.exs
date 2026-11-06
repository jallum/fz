defmodule Oracle do
  def mine(t) when t == {}, do: true
  def mine(_), do: false

  def typed(t) when t == {}, do: :yes
  def typed(_), do: :other

  def typed_nested(t) when t == {{}}, do: :yes
  def typed_nested(_), do: :other

  def sized(t) when is_tuple(t) and tuple_size(t) == 0, do: :empty
  def sized(_), do: :other

  def run do
    IO.inspect([typed({}), typed({{}}), typed({1}), typed(5)])
    IO.inspect([typed_nested({}), typed_nested({{}}), typed_nested({1}), typed_nested(5)])
    IO.inspect([sized({}), sized({{}}), sized({1}), sized(5)])
  end
end

Oracle.run()
