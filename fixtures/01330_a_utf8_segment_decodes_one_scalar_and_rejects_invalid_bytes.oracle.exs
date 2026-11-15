defmodule Utf8Head do
  def first(<<c::utf8, rest::binary>>), do: {:ok, c, rest}
  def first(other), do: {:no_match, other}

  def classify(bytes) do
    case bytes do
      <<c::utf8>> -> {:only, c}
      <<c::utf8, _::binary>> -> {:leads, c}
      _ -> :invalid
    end
  end
end

IO.inspect(Utf8Head.first("ax"))
IO.inspect(Utf8Head.first("éx"))
IO.inspect(Utf8Head.first("€x"))
IO.inspect(Utf8Head.first("😀x"))
IO.inspect(Utf8Head.first(<<0xED, 0xA0, 0x80>>))
IO.inspect(Utf8Head.first(<<0xC0, 0x80>>))
IO.inspect(Utf8Head.first(<<0xE0, 0x80, 0x80>>))
IO.inspect(Utf8Head.first(<<0xF4, 0x90, 0x80, 0x80>>))
IO.inspect(Utf8Head.first(<<0x80, 0x41>>))
IO.inspect(Utf8Head.first(<<0xE2, 0x82>>))
IO.inspect(Utf8Head.first(<<>>))
IO.inspect(Utf8Head.classify("é"))
IO.inspect(Utf8Head.classify("😀!"))
IO.inspect(Utf8Head.classify(<<0xED, 0xA0, 0x80>>))
IO.inspect(Utf8Head.classify(<<>>))
