defmodule Oracle do
  def main() do
    spawn(fn ->
      receive do
        :never -> :ok
      after
        60000 -> IO.puts("late")
      end
    end)

    IO.puts("main done")
  end
end

Oracle.main()
