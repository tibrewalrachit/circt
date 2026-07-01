# Veda — CIRCT → Lean 4 bridge for hardware formal verification

Veda imports SystemVerilog RTL into Lean 4 via CIRCT's MLIR dialects
(`hw`/`comb`/`seq`, `ltl`/`verif`) and proves temporal properties about
it — machine-checked, unbounded in time, parametric in widths — going
beyond bounded model checking. North star: OpenTitan's `prim_count`,
which circt-bmc verifies to ~20 cycles for one instance, proven
assertion-clean for all time and all parameter widths as one Lean
theorem with zero `sorry`.

## Quickstart

```sh
# Lean toolchain pinned in lean-toolchain (see toolchain.lock for all pins)
cd veda
lake build        # library + build-time axiom gate
lake exe tests    # LSpec suites

# SystemVerilog -> MLIR (needs pinned CIRCT release tools on PATH)
bridge/import.sh designs/counter/counter.sv
```

In the sandboxed dev environment, toolchain artifacts come from this
fork's `veda-tools-v1` release (mirrored by
`.github/workflows/veda-bootstrap-tools.yml`); install under
`/opt/veda-tools` and put `lean-4.31.0-linux/bin` plus
`circt-static/firtool-1.151.0/bin` on PATH.

## Layout

```
veda/
├── Veda/Core/      Design (Mealy machine), Trace, executable simulate, BitVec
├── Veda/Ltl/       (M1) denotational semantics of CIRCT ltl/verif over traces
├── Veda/Import/    (M2) generic-MLIR parser -> Core terms
├── Veda/Compose/   (M5) hw.instance composition, assume-guarantee
├── Veda/Tactics/   (M3) k-induction scaffold, bv_decide drivers
├── Veda/Ledger/    property status: Proven/Disproven/Bounded/Assumed
├── Veda/Meta/      axiom gate (#axiom_gate)
├── bridge/         SV -> canonical MLIR scripts (circt-verilog/circt-opt)
├── designs/        test RTL + checked-in round-tripped MLIR
├── harness/        (M2) 3-way differential testing: Lean sim / arcilator / Verilator
├── Tests/          LSpec suites + axiom-gate entry point
├── docs/           architecture.md, semantics-decisions.md, log/NNNN.md
└── vendor/LSpec    vendored test framework (pinned; sandbox cannot git-clone)
```

## Ground rules (abridged; see docs/architecture.md)

1. Zero `sorry`, zero added axioms in anything `proven` — enforced at
   build time by the axiom gate (bv_decide's reflection axioms allowed
   and reported; see docs/semantics-decisions.md #6).
2. Total, honest import: unknown ops become explicit `Uninterpreted`
   nodes; touched properties are auto-downgraded to `Assumed`.
3. LTL semantics mirror CIRCT docs exactly (`until` weak, `eventually`
   strong); ambiguities resolved by differential testing against
   circt-bmc and logged in docs/semantics-decisions.md.
4. Three-way differential validation of the importer; disagreement is a
   release blocker.
5. Every work session logs to docs/log/NNNN.md; commits reference log
   entries.
6. Toolchain pins live in toolchain.lock; upgrades are dedicated PRs.
