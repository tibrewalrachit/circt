import Veda
import Veda.Import.Elab

/-!
# Differential-harness driver (Lean side)

Subcommands:
* `gen <n> [seed]` — deterministic pseudo-random stimulus, one
  `rst en` pair per line (0/1).
* `run <generic.mlir> <stim.txt>` — import the design and simulate it
  from the all-zeros state, printing each cycle's outputs (decimal,
  space-separated). This exercises the *real* importer + interpreter
  path, so agreement with Verilator/arcilator is evidence about the
  importer (rule 4).
* `arc-tb <hw.mlir> <stim.txt>` — emit an MLIR testbench that drives
  the same stimulus through arcilator's `arc.sim` JIT (`--run`).
  Port order and clocking follow the harness convention: outputs are
  sampled with `clk` low, then a posedge is applied.

Input port convention (counter): ports [clk, rst, en]; the stimulus
drives rst/en, the harness supplies the clock.
-/

open Veda Veda.Import

def lcgNext (x : Nat) : Nat := (x * 1103515245 + 12347) % 2147483648

def genStim (n : Nat) (seed : Nat) : List (Bool × Bool) :=
  (List.range n).foldl
    (fun (acc : List (Bool × Bool) × Nat) _ =>
      let x := lcgNext acc.2
      (acc.1 ++ [((x / 65536) % 4 == 0, (x / 131072) % 2 == 0)], x))
    ([], seed) |>.1

def parseStim (text : String) : List (Bool × Bool) :=
  (text.splitOn "\n").filterMap fun line =>
    match (line.splitOn " ").filterMap (·.toNat?) with
    | [r, e] => some (r == 1, e == 1)
    | _ => none

def boolBit (b : Bool) : String := if b then "1" else "0"

/-- Simulate the imported circuit, printing outputs per cycle. Inputs
are [clk, rst, en] per the counter's port order; clk is driven as 1
(the interpreter's tick *is* the posedge; the clock value is unused). -/
def runLean (mlir stim : String) : IO UInt32 := do
  match importCircuit mlir with
  | .error e => IO.eprintln s!"import error: {e}"; return 1
  | .ok c =>
    if c.inputs.map Prod.fst != ["clk", "rst", "en"] then
      IO.eprintln s!"unexpected port list: {c.inputs}"; return 1
    let mut s := c.zeroState
    for (rst, en) in parseStim stim do
      let ins : List Val :=
        [⟨1, 1#1⟩, ⟨1, if rst then 1#1 else 0#1⟩, ⟨1, if en then 1#1 else 0#1⟩]
      let outs := c.outFn s ins
      IO.println (" ".intercalate (outs.map fun v => toString v.2.toNat))
      s := c.stepFn s ins
    return 0

/-- Emit an arcilator `arc.sim` testbench for the counter: the hw
module source followed by a `main` that replays the stimulus. -/
def emitArcTb (hwMlir stim : String) : IO Unit := do
  -- Strip a `module { ... }` wrapper so the hw.module symbol shares
  -- the testbench func's symbol table.
  let lines := hwMlir.splitOn "\n"
  let body :=
    if (lines.headD "").trimAscii.toString == "module {" then
      let inner := lines.drop 1
      let inner := inner.take (inner.length -
        (inner.reverse.findIdx? (·.trimAscii.toString == "}") |>.getD 0) - 1)
      "\n".intercalate inner
    else hwMlir
  IO.println body
  IO.println "func.func @main() {"
  IO.println "  %false = arith.constant 0 : i1"
  IO.println "  %true = arith.constant 1 : i1"
  IO.println "  arc.sim.instantiate @counter as %model {"
  let inst := "!arc.sim.instance<@counter>"
  let mut i := 0
  for (rst, en) in parseStim stim do
    let r := if rst then "%true" else "%false"
    let e := if en then "%true" else "%false"
    IO.println s!"    arc.sim.set_input %model, \"rst\" = {r} : i1, {inst}"
    IO.println s!"    arc.sim.set_input %model, \"en\" = {e} : i1, {inst}"
    IO.println s!"    arc.sim.set_input %model, \"clk\" = %false : i1, {inst}"
    IO.println s!"    arc.sim.step %model : {inst}"
    IO.println s!"    %v{i} = arc.sim.get_port %model, \"count\" : i8, {inst}"
    IO.println s!"    arc.sim.emit \"count\", %v{i} : i8"
    IO.println s!"    arc.sim.set_input %model, \"clk\" = %true : i1, {inst}"
    IO.println s!"    arc.sim.step %model : {inst}"
    i := i + 1
  IO.println "  }"
  IO.println "  return"
  IO.println "}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["gen", n] | ["gen", n, _] =>
    let seed := (args[2]?.bind (·.toNat?)).getD 20260701
    for (rst, en) in genStim (n.toNat?.getD 100) seed do
      IO.println s!"{boolBit rst} {boolBit en}"
    return 0
  | ["run", mlirPath, stimPath] =>
    runLean (← IO.FS.readFile mlirPath) (← IO.FS.readFile stimPath)
  | ["arc-tb", hwPath, stimPath] =>
    emitArcTb (← IO.FS.readFile hwPath) (← IO.FS.readFile stimPath)
    return 0
  | _ =>
    IO.eprintln "usage: harness gen <n> [seed] | run <generic.mlir> <stim> | arc-tb <hw.mlir> <stim>"
    return 1
