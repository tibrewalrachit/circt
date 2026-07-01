# Differential testing harness (lands in M2)

Three-way differential validation of the importer on shared stimulus:

1. **Lean executable semantics** — `Design.simulate` on the imported design
   (tied to the trace semantics by `Veda.Design.simulate_getElem`).
2. **arcilator** — CIRCT's cycle-based simulator, run on the same
   `hw`/`comb`/`seq` MLIR the importer consumed.
3. **Verilator** — run on the original SystemVerilog source.

Plan: a driver generates N random stimulus steps per design in
`veda/designs/`, feeds all three simulators, and compares outputs
bit-exactly at every cycle. Any disagreement is a release blocker
(non-negotiable rule 4).
