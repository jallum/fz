lit = fn
  <<"true", rest :: binary>> -> {:true_lit, rest}
  <<"null", rest :: binary>> -> {:null_lit, rest}
  bin -> {:no, bin}
end

ws = fn
  <<" ", rest :: binary>> -> {:space, rest}
  <<"\n", rest :: binary>> -> {:newline, rest}
  bin -> {:no, bin}
end

annotated = fn
  <<"ab" :: binary, rest :: binary>> -> {:annotated, rest}
  bin -> {:no, bin}
end

byte_form = fn
  <<34, rest :: binary>> -> {:quote, rest}
  bin -> {:no, bin}
end

sized = fn
  <<x :: binary-size(2), rest :: binary>> -> {:sized, x, rest}
  bin -> {:no, bin}
end

IO.inspect(lit.("true,x"))
IO.inspect(lit.("null"))
IO.inspect(lit.("false"))

IO.inspect(ws.(" abc"))
IO.inspect(ws.("\nabc"))
IO.inspect(ws.("abc"))

IO.inspect(annotated.("abcd"))
IO.inspect(annotated.("xy"))

IO.inspect(byte_form.("\"hi\""))
IO.inspect(sized.("abcd"))
