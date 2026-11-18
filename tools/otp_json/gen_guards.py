# prints the defguardp block of json.hrl in Elixir form
esc = list(range(0,32)) + [34, 92]
plain = [32,33] + list(range(35,92)) + list(range(93,128))
def chain(var, xs):
    return " or\n      ".join(f"{var} === {x}" for x in xs)
print("""  # json.hrl
  defguardp is_1_to_9(x)
            when x === ?1 or
                   x === ?2 or
                   x === ?3 or
                   x === ?4 or
                   x === ?5 or
                   x === ?6 or
                   x === ?7 or
                   x === ?8 or
                   x === ?9

  defguardp is_0_to_9(x) when x >= ?0 and x <= ?9

  # erl: -define(is_ws(X), X =:= $\\s; X =:= $\\t; X =:= $\\r; X =:= $\\n).
  defguardp is_ws(x) when x === ?\\s or x === ?\\t or x === ?\\r or x === ?\\n
""")
print("  defguardp is_ascii_escape(byte)\n            when " + chain("byte", esc).replace("\n      ", "\n                   ") + "\n")
print("  defguardp is_ascii_plain(byte)\n            when " + chain("byte", plain).replace("\n      ", "\n                   ") + "\n")
print("""  defguardp are_all_ascii_plain(b1, b2, b3, b4, b5, b6, b7, b8)
            when is_ascii_plain(b1) and
                   is_ascii_plain(b2) and
                   is_ascii_plain(b3) and
                   is_ascii_plain(b4) and
                   is_ascii_plain(b5) and
                   is_ascii_plain(b6) and
                   is_ascii_plain(b7) and
                   is_ascii_plain(b8)
""")
