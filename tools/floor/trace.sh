#!/bin/zsh
# usage: trace.sh EXAMPLE[@FUNCTION]...  (FUNCTION defaults to loop)
# -> target/floor/EXAMPLE.trace (one steady-state iteration of Main.loop, every
# executed instruction) and a per-function summary on stdout. Needs target/floor/EXAMPLE.fz.bin from measure.sh.
HERE=${0:A:h}; OUT=${HERE:h:h}/target/floor
for ex in "$@"; do
  fn=loop; [[ $ex == *@* ]] && { fn=${ex#*@}; ex=${ex%@*}; }
  ex=${ex:t:r}; bin=$OUT/$ex.fz.bin
  sym=$(nm -n $bin | awk -v f="_${fn}__" '$2=="T" && $3 ~ /^_fz_fn_[0-9]+_/ && index($3,f) && $3 !~ /resume/ {print substr($3,2); exit}')
  [[ -n $sym ]] || { echo "NO LOOP SYMBOL $ex"; exit 1; }
  /usr/bin/python3 $HERE/trace.py $bin $sym 0 12000 1000 > $OUT/$ex.trace 2> $OUT/$ex.trace.err || { echo "TRACE FAIL $ex"; tail -3 $OUT/$ex.trace.err; exit 1; }
  echo "== $ex ($(wc -l < $OUT/$ex.trace | tr -d ' ') instructions)"
  awk '{s=$NF; sub(/\+0x[0-9a-f]+$/,"",s); sub(/\+EXT$/,"",s); if (s ~ /^_fz_fn_/) s="compiled code"; if (s!=p) {e[s]++; if(!(s in o)) {o[s]=++k; name[k]=s}} c[s]++; p=s} END {for(i=1;i<=k;i++) printf "  %-56s %5d  x%d\n", substr(name[i],1,56), c[name[i]], e[name[i]]}' $OUT/$ex.trace
done
