four = "caf\u00e9"
braced = "caf\u{e9}"
IO.inspect({four, braced, four == braced, byte_size(four), String.length(four)})
emoji = "\u{1F600}"
IO.inspect({emoji, byte_size(emoji), String.length(emoji)})
IO.inspect({"\u{0041}\u0042\u{43}", "a\u{10FFFF}b" == "a" <> <<244, 143, 191, 191>> <> "b"})
IO.inspect(:"caf\u00e9" == :café)
IO.inspect("""
\u00e9 and \u{1F600}
""")
IO.inspect("e\u0301" == <<101, 204, 129>>)
