import Std.Tactic.BVDecide

/-!
# BitVec utilities

Helpers for the `BitVec`-heavy designs produced by the importer, plus a
smoke test that the `bv_decide` pipeline (bitblasting + bundled SAT solver
+ kernel-checked LRAT certificate) works in this environment. `bv_decide`
is the workhorse for ground/bounded obligations throughout Veda.
-/

namespace Veda

/-- `bv_decide` smoke test: 8-bit increment wraps at 255. If this file
builds, the SAT solver and LRAT checker are functional. -/
theorem bv_smoke_wrap (x : BitVec 8) : x + 1 = 0 ↔ x = 255 := by
  bv_decide

/-- A second smoke test exercising subtraction and comparison. -/
theorem bv_smoke_sub_lt (x : BitVec 8) (h : x ≠ 0) : x - 1 < x := by
  bv_decide

end Veda
