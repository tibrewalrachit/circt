# Veda architecture (M0 snapshot)

Veda imports SystemVerilog RTL into Lean 4 via CIRCT's MLIR dialects and
proves temporal properties with machine-checked, unbounded, parametric
proofs. AI agents write the proofs; the Lean kernel is the sole arbiter.

## Pipeline

```
counter.sv ──circt-verilog──► hw/comb/seq MLIR ──circt-opt (generic)──►
counter.generic.mlir ──Veda/Import (M2)──► Veda.Design ──Veda/Ltl (M1/M3)──►
Prop' terms ──proofs (bv_decide, k-induction)──► ledger: Proven/…
```

Cross-checks, never trust anchors: Verilator and arcilator (differential
simulation, M2), circt-bmc (bounded verdict agreement, M3).

## Trust story

What you must trust for a `Proven` entry in the ledger:

1. **The Lean kernel** (and its three standard axioms).
2. **The Lean compiler, for `bv_decide` obligations only.** The SAT
   solver's LRAT certificate is checked by a formally verified checker,
   but that checker runs as compiled native code (`.../_native.bv_decide.*`
   axioms). The axiom gate prints exactly which theorems carry this trust;
   everything else is kernel-only. See semantics-decisions.md #6.
3. **The importer (`Veda/Import`) is the TCB boundary**: the claim is
   about the imported `Design`, and it describes the RTL only insofar as
   the importer's semantics for each MLIR op is faithful to CIRCT's. This
   is why rule 4 (three-way differential validation) exists — simulation
   agreement is evidence about importer fidelity, the one thing the
   kernel cannot check for us.

What you do *not* have to trust: circt-bmc, Z3, Verilator, arcilator —
they are cross-checks; disagreement blocks a release but their answers
are never cited as proof. External-tool counterexamples only count once
replayed through `Design.simulate`.

Enforcement: `lake build` elaborates `Tests/AxiomGate.lean`, which runs
`#axiom_gate Veda` over every declaration in the library — `sorry` or a
user axiom is a red build (Veda/Meta/AxiomGate.lean).

## Status ledger

`Veda.Status`: `proven | disproven (witness) | bounded (depth) | assumed
(reason)`. Rules: only kernel-checked theorems are `proven`; any property
whose cone of influence touches an `Uninterpreted` import node is
auto-downgraded to `assumed`; `disproven` requires a trace that replays
through the Lean executable semantics. Report generation lands in M5.

## Repository layout

See veda/README.md. The Lean library lives under `Veda/`; external tools
are pinned in `toolchain.lock` and mirrored to this fork's
`veda-tools-v1` release for the sandboxed dev environment (see
docs/log/0001.md for why).

## Milestone state

- **M0 (this snapshot): done.** Toolchain pinned; core `Design`/`Trace`/
  `simulate` with 12 proved lemmas; axiom gate; LSpec suites; counter
  round-tripped to generic MLIR; CI green.
- M1 ltl semantics → M2 importer + differential harness → M3 BMC
  cross-check + k-induction → M4 prim_count unbounded & parametric →
  M5 composition + ledger report → M6 invariant-synthesis loop.
