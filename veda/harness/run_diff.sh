#!/usr/bin/env bash
# Three-way differential harness: Lean executable semantics vs
# Verilator vs arcilator on shared random stimulus (rule 4 — any
# disagreement is a release blocker).
#
# Usage: harness/run_diff.sh [nsteps] [seed]
# Requires on PATH: lake (Lean), verilator, arcilator.
# Run from the veda/ directory.
set -euo pipefail

steps=${1:-10000}
seed=${2:-20260701}
work=.lake/harness
mkdir -p "$work"

echo "== generating $steps stimulus steps (seed $seed)"
lake exe harness gen "$steps" "$seed" > "$work/stim.txt"

echo "== Lean executable semantics (imported design)"
lake exe harness run designs/counter/counter.generic.mlir "$work/stim.txt" \
  > "$work/lean.out"

echo "== Verilator"
verilator --cc --exe --build -j 2 -Mdir "$work/obj_dir" \
  --top-module counter designs/counter/counter.sv "$PWD/harness/counter_tb.cpp" \
  -o Vcounter_tb > /dev/null
"$work/obj_dir/Vcounter_tb" "$work/stim.txt" > "$work/verilator.out"

echo "== arcilator (arc.sim JIT)"
lake exe harness arc-tb designs/counter/counter.hw.mlir "$work/stim.txt" \
  > "$work/arc_tb.mlir"
arcilator "$work/arc_tb.mlir" --run --jit-entry=main \
  | awk '{ print $3 }' \
  | while read -r h; do echo $((16#$h)); done > "$work/arcilator.out"

echo "== comparing"
diff -q "$work/lean.out" "$work/verilator.out"
diff -q "$work/lean.out" "$work/arcilator.out"
echo "OK: three-way bit-exact agreement over $steps cycles"
