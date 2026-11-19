#!/bin/zsh
# usage: targets.sh [test]
# Builds the hand-written targets, runs their reference test (every target against plain C
# over random inputs), and prints each target's instructions per iteration: the slope
# between 10M and 30M iterations. "test" stops after the reference test.
HERE=${0:A:h}; OUT=${HERE:h:h}/target/floor; mkdir -p $OUT
cc -O2 -o $OUT/targets $HERE/targets/harness.c $HERE/targets/targets.s || exit 1
$OUT/targets test || exit 1
[[ $1 == test ]] && exit 0
for t in empty byte_size byte_size_view byte_size_today eq_small eq_large eq_same eq_length eqw_small eqw_large eqw_length eqw_literal eqw_differ match_tail match_sum concat send_self interp ctor_byte ctor_segments slice append through_call; do
  for n in 10000000 30000000; do /usr/bin/time -l $OUT/targets $t $n > /dev/null 2> $OUT/targets.err || { echo "RUN FAIL $t"; exit 1; }; eval "i$n=$(awk '/instructions retired/ {print $1}' $OUT/targets.err)"; done
  printf '%-18s %6.1f\n' $t $(( (i30000000 - i10000000) / 20000000.0 ))
done
