defmodule Oracle do
  def run() do
    f =
      fn ss ->
        IO.inspect(:fn_first)
        counts = ss
        IO.inspect(:fn_second)
        counts
      end

    IO.inspect(f.([1]))

    g =
      fn
        0 ->
          IO.inspect(:fn_zero)
          :zero
        n ->
          IO.inspect(:fn_other)
          m = n + 1
          IO.inspect(m)
          m
      end

    IO.inspect({g.(0), g.(4)})

    h =
      fn x, y ->
        IO.inspect(:fn_pair)
        x + y
      end

    IO.inspect(h.(1, 2))

    IO.inspect(
      case 2 do
        1 ->
          IO.inspect(:case_one)
          :one
        n ->
          IO.inspect(:case_first)
          k = n * 10
          IO.inspect(:case_second)
          k
      end
    )

    send(self(), 5)

    IO.inspect(
      receive do
        m ->
          IO.inspect(:receive_first)
          r = m + 1
          IO.inspect(:receive_second)
          r
      end
    )

    limit = 3

    IO.inspect(
      cond do
        limit > 5 ->
          IO.inspect(:cond_skipped)
          :skipped
        limit > 1 ->
          IO.inspect(:cond_first)
          c = 3
          IO.inspect(:cond_second)
          c
      end
    )

    IO.inspect(
      with {:ok, a} <- {:error, 9} do
        a
      else
        {:error, e} ->
          IO.inspect(:else_first)
          w = e + 1
          IO.inspect(:else_second)
          w
      end
    )

    IO.inspect(
      case 3 do
        n ->
          inner = fn z ->
            IO.inspect(:nested_fn)
            z + 1
          end

          case inner.(n) do
            4 ->
              IO.inspect(:nested_case)
              :four
          end
      end
    )
  end
end

Oracle.run()
