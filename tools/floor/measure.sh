#!/bin/zsh
# usage: measure.sh [-f FZ2] [-n N1] [-m N2] [-s beam|fz|both] EXAMPLE...
# Prints, per example and side, instructions per iteration: the slope of
# "instructions retired" between run lengths N1 and N2, so start-up cancels.
# Exits non-zero if any build or run fails, or the two sides print different results.
# FZ2 defaults to target/release/fz2; build output and run logs go to target/floor.
HERE=${0:A:h}; ROOT=${HERE:h:h}
# fz is run once per length (its counts repeat to the instruction). The BEAM is
# run three times per length and the lowest count kept: its boot varies by tens
# of millions of instructions, so it also gets longer runs (B1, B2).
# An example may override fz's lengths with a "# fz-n: N1 N2" line, or both
# sides' lengths with "# n: N1 N2" (growing results: cost depends on length).
FZ2=$ROOT/target/release/fz2; N1=1000000; N2=3000000; B1=10000000; B2=50000000; SIDE=both
while getopts f:n:m:s: o; do case $o in f) FZ2=$OPTARG;; n) N1=$OPTARG;; m) N2=$OPTARG;; s) SIDE=$OPTARG;; esac; done
BEAM=(elixir --erl "+S 1:1 +sbwt none +sbwtdcpu none +sbwtdio none")
lowest() { # lowest LABEL N CMD... -> REPLY is the lowest of three counts
  local best=0 i; for i in 1 2 3; do instr "$@"; (( best == 0 || REPLY < best )) && best=$REPLY; done; REPLY=$best
}
shift $((OPTIND-1))
OUT=$ROOT/target/floor; mkdir -p $OUT
instr() { # instr LABEL N CMD... -> sets REPLY to instructions retired, RESULT to stdout
  local label=$1 n=$2; shift 2
  /usr/bin/time -l "$@" $n > $OUT/$label.$n.out 2> $OUT/$label.$n.err || { echo "RUN FAIL $label n=$n"; tail -5 $OUT/$label.$n.err; exit 1; }
  REPLY=$(awk '/instructions retired/ {print $1}' $OUT/$label.$n.err)
  RESULT=$(tail -1 $OUT/$label.$n.out)
}
for ex in "$@"; do
  ex=${ex:t:r}; src=$HERE/programs/$ex.exs; line="$ex"
  if [[ $SIDE != fz ]]; then
    b1=$B1; b2=$B2; o=($(awk '/^# n:/ {print $3, $4}' $src)); (( $#o == 2 )) && { b1=$o[1]; b2=$o[2]; }
    lowest $ex.beam $b1 $BEAM $src; a=$REPLY
    lowest $ex.beam $b2 $BEAM $src; b=$REPLY
    line="$line beam=$(printf '%.1f' $(( (b - a) / (b2 - b1 + 0.0) )))"
  fi
  if [[ $SIDE != beam ]]; then
    $FZ2 build -o $OUT/$ex.fz.bin $src > $OUT/$ex.fz.build 2>&1 || { echo "BUILD FAIL $ex"; tail -8 $OUT/$ex.fz.build; exit 1; }
    f1=$N1; f2=$N2; o=($(awk '/^# fz-n:/ {print $3, $4}' $src)); (( $#o == 2 )) && { f1=$o[1]; f2=$o[2]; }
    o=($(awk '/^# n:/ {print $3, $4}' $src)); (( $#o == 2 )) && { f1=$o[1]; f2=$o[2]; }
    instr $ex.fz $f1 $OUT/$ex.fz.bin; a=$REPLY
    instr $ex.fz $f2 $OUT/$ex.fz.bin; b=$REPLY
    line="$line fz=$(printf '%.1f' $(( (b - a) / (f2 - f1 + 0.0) )))"
  fi
  if [[ $SIDE == both ]]; then
    instr $ex.beam 10000 $BEAM $src; beam_result=$RESULT
    instr $ex.fz 10000 $OUT/$ex.fz.bin
    [[ $beam_result == $RESULT ]] || { echo "RESULT MISMATCH $ex at n=10000: beam=$beam_result fz=$RESULT"; exit 1; }
  fi
  echo "$line"
done
