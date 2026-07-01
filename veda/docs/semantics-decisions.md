# Semantics decisions

Running record of every semantic choice where CIRCT documentation is
ambiguous, or where Veda fixes a convention. Each entry: the decision,
why, and how it was (or will be) validated. Differential testing against
circt-bmc is the arbiter for LTL questions (non-negotiable rule 3).

## 1. Time model: Nat-indexed traces at active clock edges (M0)

`Trace D := Nat → StateTy × InputTy`; tick `n` is the n-th active clock
edge of the design's single clock domain. Multi-clock designs are out of
scope until a dedicated decision extends this. Traces are infinite — this
is what "unbounded" means throughout Veda.

## 2. Reset states are a predicate, not a value (M0)

`Design.init : StateTy → Prop`. Designs with undefined power-on values
(e.g. `seq.firreg` without reset) get `init := fun _ => True` for those
components rather than an arbitrary concrete value — no silent
approximation (rule 2). Registers with synchronous reset keep the reset
mux inside `step`, exactly as `circt-verilog` emits it (see
designs/counter: reset is a mux in the fan-in of the register).

## 3. Mealy convention (M0)

`out s i` is observed in the same tick as `(s, i)`; `step s i` is the
state after that tick's active edge. This matches arcilator's cycle
semantics and Verilator's per-posedge sampling for the harness; the M2
differential run validates the alignment bit-exactly.

## 4. ltl.until is weak, ltl.eventually is strong (M0, from CIRCT docs)

Stated explicitly in docs/Dialects/LTL.md ("Until and Eventually").
Veda/Ltl must encode: `until p q` holds even if `q` never fires provided
`p` holds forever; `eventually p` requires an actual witness tick.
Validation: M3 BMC cross-check.

## 5. LTL doc oddities to resolve by differential testing (open)

- The SVA mapping table shows `always p` ⇒ `ltl.repeat %p, 0` (a
  *sequence* op used as G) and `p1 until p2 : !ltl.sequence` — both look
  like type-level typos in the doc; op definitions say `until` yields a
  property. Resolution plan: import `assert property (always ...)` /
  `until` examples through `circt-verilog` in M3 and inspect the actual
  ops emitted; record the answer here.
- `ltl.delay` with omitted length is unbounded-but-finite (`##[N:$]`) —
  the "finite amount of cycles" phrasing matters for the Lean encoding
  (∃ k ≥ N, ...), not (∀-eventually). Cross-check with circt-bmc verdicts
  on small unbounded-delay properties.

## 6. bv_decide's compiled-reflection axioms are allowed, but reported (M0)

Rule 1 demands standard axioms only; the milestone plan simultaneously
mandates `bv_decide` as the workhorse. These conflict: on Lean v4.31.0,
`bv_decide` records a per-theorem axiom (`<thm>._native.bv_decide.*`,
the successor of `Lean.ofReduceBool`) because the LRAT certificate is
checked by a *formally verified* checker that is *executed as compiled
native code* rather than by kernel reduction. Decision: the axiom gate
(Veda/Meta/AxiomGate.lean) accepts exactly this axiom class and prints
every declaration relying on it in the build log; everything else beyond
{propext, Classical.choice, Quot.sound} — including `sorryAx` — is a hard
build failure. Trust implications documented in architecture.md. If a
future toolchain offers kernel-only LRAT checking at acceptable cost, we
switch and delete this entry.

## 7. Two-state values only at the hw/comb/seq level (M0)

Veda imports the post-`MooreToCore` `hw`/`comb`/`seq` IR, which is
two-state (`iN`). Four-state `moore.lN` values never reach the importer
in this pipeline; if a future design imports at the `moore` level or a
2-state coercion is known to be lossy for a property, that property is
downgraded to `Assumed` with the reason recorded (rule 2).
