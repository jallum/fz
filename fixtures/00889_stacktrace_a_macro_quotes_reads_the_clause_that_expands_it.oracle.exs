defmodule Trace do
  defmacro is_a_list() do
    quote do: is_list(__STACKTRACE__)
  end
end
defmodule User do
  require Trace
  def run() do
    try do
      raise ArgumentError, "boom"
    rescue
      _ -> Trace.is_a_list()
    end
  end
end
IO.inspect(User.run())
