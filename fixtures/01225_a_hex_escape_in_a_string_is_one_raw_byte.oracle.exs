high = "\xFF"
IO.inspect({high, high == <<255>>, byte_size(high), String.valid?(high)})
IO.inspect({"\xe9" == <<233>>, "caf\xc3\xa9" == "café", "A\xFFB" == <<65, 255, 66>>})
IO.inspect({"\x414" == <<65, 52>>, "\x4" == <<4>>, "\x4g" == <<4, 103>>})
IO.inspect({"\x{e9}" == <<195, 169>>, "\x{FF}" == <<195, 191>>, "\x{1F600}" == "\u{1F600}"})
IO.inspect("""
\xFF-\x41
""" == <<255, 45, 65, 10>>)
case "A\xFFB" do
  <<65, byte, 66>> -> IO.inspect(byte)
end
IO.inspect("A\xFFB" <> "!" == <<65, 255, 66, 33>>)
