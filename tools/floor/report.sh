#!/bin/zsh
# usage: report.sh [-f FZ2] [-s fz|both] [PROGRAM...]   (default: every program, both sides)
# One row per program: fz's instructions per iteration, the hand-written target named by the
# program's "# target:" line, how far fz is above it, and the BEAM. A program that does not
# build or run, or whose two sides print different results, prints its failure as its row
# and the command exits non-zero.
HERE=${0:A:h}; SIDE=both; FZ=()
while getopts f:s: o; do case $o in f) FZ=(-f $OPTARG);; s) SIDE=$OPTARG;; esac; done
shift $((OPTIND-1))
(( $# )) || set -- $HERE/programs/*.exs
typeset -A floor
$HERE/targets.sh | while read name count; do floor[$name]=$count; done
(( $#floor )) || { echo "TARGETS FAIL"; exit 1; }
printf '%-30s %9s %8s %8s %9s\n' program fz target above beam
failed=0
for src in "$@"; do
  ex=${src:t:r}; src=$HERE/programs/$ex.exs
  row=$($HERE/measure.sh $FZ -s $SIDE $ex) || { echo "$row"; failed=1; continue; }
  fz=${${(M)${=row}:#fz=*}#fz=}; beam=${${(M)${=row}:#beam=*}#beam=}
  target=$(awk '/^# target:/ {print $3}' $src); t=${floor[$target]:--}; above=-
  [[ $t != - ]] && above=$(printf '%.1f' $(( fz - t )))
  printf '%-30s %9s %8s %8s %9s\n' $ex $fz $t $above ${beam:--}
done
exit $failed
