import Veda.Core.Trace
import Veda.Ltl.Syntax

/-!
# Denotational semantics of the ltl fragment over traces

Sequences are interpreted by a *length-indexed match relation*:
`SMatch t s i len` means sequence `s` matches trace `t` on the tick
interval starting at `i` and spanning `len` ticks (so the match *ends* on
tick `i + len - 1`; `len = 0` is an empty match, producible only by
`rep _ 0 _`). This is the standard "tight satisfaction" reading of SVA
sequences, with CIRCT's `##0`-fusion for `concat`.

Properties are interpreted at a tick by `sat`; `holds` quantifies over
all valid traces at tick 0 (the reset tick). Key semantic commitments,
each recorded in docs/semantics-decisions.md:

* `concat` requires non-empty operands and overlaps end/start
  (#7) — in particular fusion of two booleans is their conjunction,
  proved below (`smatch_concat_atom`), matching the CIRCT doc's
  "`a ##0 b` ≡ `a && b` for booleans".
* sequence-as-property is strong match existence (#8).
* `until'` is weak and non-overlapping ("every cycle *before* the first
  cycle `q` holds"), `eventually` is strong — per CIRCT docs.
-/

namespace Veda

variable {D : Design}

/-- `k` back-to-back matches of a sequence (whose match relation at a
given start/length is `M`), each starting the tick after the previous one
ends (`##1` separation, per SVA consecutive repetition). Total length is
the sum of the parts. -/
def RepMatch (M : Nat → Nat → Prop) : Nat → Nat → Nat → Prop
  | 0, _, len => len = 0
  | k + 1, i, len => ∃ l₁ l₂, M i l₁ ∧ RepMatch M k (i + l₁) l₂ ∧ len = l₁ + l₂

/-- Does `d` lie in the CIRCT delay/repeat window `(n, w)`? -/
def inWindow (n : Nat) (w : Option Nat) (d : Nat) : Prop :=
  n ≤ d ∧ match w with
    | none => True
    | some wnd => d ≤ n + wnd

/-- Tight match: sequence `s` matches `t` starting at tick `i`, spanning
`len` ticks. -/
def SMatch (t : Trace D) : Seq D → Nat → Nat → Prop
  | .atom f, i, len => len = 1 ∧ f (t.state i) (t.input i) = true
  | .delay s n w, i, len =>
      ∃ d len', inWindow n w d ∧ len = d + len' ∧ SMatch t s (i + d) len'
  | .concat a b, i, len =>
      ∃ la lb, 1 ≤ la ∧ 1 ≤ lb ∧ len + 1 = la + lb ∧
        SMatch t a i la ∧ SMatch t b (i + la - 1) lb
  | .or a b, i, len => SMatch t a i len ∨ SMatch t b i len
  | .and a b, i, len =>
      ∃ la lb, SMatch t a i la ∧ SMatch t b i lb ∧ len = max la lb
  | .intersect a b, i, len => SMatch t a i len ∧ SMatch t b i len
  | .rep s n w, i, len =>
      ∃ k, inWindow n w k ∧ RepMatch (SMatch t s) k i len

/-- Satisfaction of a property at tick `i` of trace `t`. -/
def sat (t : Trace D) : Prop' D → Nat → Prop
  | .seq s, i => ∃ len, SMatch t s i len
  | .not p, i => ¬ sat t p i
  | .and p q, i => sat t p i ∧ sat t q i
  | .or p q, i => sat t p i ∨ sat t q i
  | .imp s p, i =>
      ∀ len, 1 ≤ len → SMatch t s i len → sat t p (i + len - 1)
  | .until' p q, i =>
      ∀ j, i ≤ j → (∀ k, i ≤ k → k ≤ j → ¬ sat t q k) → sat t p j
  | .eventually p, i => ∃ j, i ≤ j ∧ sat t p j
  | .always p, i => ∀ j, i ≤ j → sat t p j

/-- A property holds of a design: satisfied at the reset tick of every
valid trace. `assert property` obligations are imported with an explicit
`always` wrapper (docs/semantics-decisions.md #9). -/
def holds (D : Design) (p : Prop' D) : Prop :=
  ∀ t : Trace D, Trace.valid D t → sat t p 0

/-! ## Basic lemmas -/

section Lemmas

variable (t : Trace D)

@[simp] theorem smatch_atom_iff (f : D.StateTy → D.InputTy → Bool)
    (i len : Nat) :
    SMatch t (.atom f) i len ↔ len = 1 ∧ f (t.state i) (t.input i) = true :=
  Iff.rfl

@[simp] theorem sat_seq_iff (s : Seq D) (i : Nat) :
    sat t (.seq s) i ↔ ∃ len, SMatch t s i len := Iff.rfl

@[simp] theorem sat_not_iff (p : Prop' D) (i : Nat) :
    sat t (.not p) i ↔ ¬ sat t p i := Iff.rfl

@[simp] theorem sat_and_iff (p q : Prop' D) (i : Nat) :
    sat t (.and p q) i ↔ sat t p i ∧ sat t q i := Iff.rfl

@[simp] theorem sat_or_iff (p q : Prop' D) (i : Nat) :
    sat t (.or p q) i ↔ sat t p i ∨ sat t q i := Iff.rfl

@[simp] theorem sat_always_iff (p : Prop' D) (i : Nat) :
    sat t (.always p) i ↔ ∀ j, i ≤ j → sat t p j := Iff.rfl

@[simp] theorem sat_eventually_iff (p : Prop' D) (i : Nat) :
    sat t (.eventually p) i ↔ ∃ j, i ≤ j ∧ sat t p j := Iff.rfl

/-- A boolean atom as a property: satisfied iff the signal is true now. -/
theorem sat_atom_iff (f : D.StateTy → D.InputTy → Bool) (i : Nat) :
    sat t (.seq (.atom f)) i ↔ f (t.state i) (t.input i) = true := by
  constructor
  · rintro ⟨len, _, hf⟩; exact hf
  · intro hf; exact ⟨1, rfl, hf⟩

/-- Fusion of two booleans is their conjunction — the CIRCT doc's
"`a ##0 b` is equivalent to `a && b`" for boolean operands. -/
theorem smatch_concat_atom (f g : D.StateTy → D.InputTy → Bool)
    (i len : Nat) :
    SMatch t (.concat (.atom f) (.atom g)) i len ↔
      len = 1 ∧ (f (t.state i) (t.input i) && g (t.state i) (t.input i)) = true := by
  constructor
  · rintro ⟨la, lb, _, _, hlen, ⟨ha1, hfa⟩, hb⟩
    subst ha1
    obtain ⟨hb1, hgb⟩ := hb
    subst hb1
    refine ⟨by omega, ?_⟩
    simpa [hfa] using hgb
  · rintro ⟨hlen, hfg⟩
    subst hlen
    rw [Bool.and_eq_true] at hfg
    exact ⟨1, 1, Nat.le_refl 1, Nat.le_refl 1, rfl, ⟨rfl, hfg.1⟩, ⟨rfl, hfg.2⟩⟩

/-- `##[0:0]` is the identity on sequences. -/
theorem smatch_delay_zero_iff (s : Seq D) (i len : Nat) :
    SMatch t (.delay s 0 (some 0)) i len ↔ SMatch t s i len := by
  constructor
  · rintro ⟨d, len', ⟨-, hle⟩, hlen, hm⟩
    have hd : d = 0 := by omega
    subst hd
    have hl : len = len' := by omega
    subst hl
    simpa using hm
  · intro hm
    exact ⟨0, len, by simp [inWindow], by omega, by simpa using hm⟩

/-- `always` eliminates to the current tick. -/
theorem sat_always_elim {p : Prop' D} {i : Nat} (h : sat t (.always p) i) :
    sat t p i := h i (Nat.le_refl i)

/-- `always` is idempotent. -/
theorem sat_always_always_iff (p : Prop' D) (i : Nat) :
    sat t (.always (.always p)) i ↔ sat t (.always p) i := by
  constructor
  · intro h j hj
    exact h i (Nat.le_refl i) j hj
  · intro h j hj k hk
    exact h k (Nat.le_trans hj hk)

/-- `always` distributes over conjunction. -/
theorem sat_always_and_iff (p q : Prop' D) (i : Nat) :
    sat t (.always (.and p q)) i ↔
      sat t (.and (.always p) (.always q)) i := by
  constructor
  · intro h
    exact ⟨fun j hj => (h j hj).1, fun j hj => (h j hj).2⟩
  · rintro ⟨hp, hq⟩ j hj
    exact ⟨hp j hj, hq j hj⟩

/-- `eventually` distributes over disjunction. -/
theorem sat_eventually_or_iff (p q : Prop' D) (i : Nat) :
    sat t (.eventually (.or p q)) i ↔
      sat t (.or (.eventually p) (.eventually q)) i := by
  constructor
  · rintro ⟨j, hj, h | h⟩
    · exact Or.inl ⟨j, hj, h⟩
    · exact Or.inr ⟨j, hj, h⟩
  · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
    · exact ⟨j, hj, Or.inl h⟩
    · exact ⟨j, hj, Or.inr h⟩

/-- `eventually` is introduced by the present. -/
theorem sat_eventually_intro {p : Prop' D} {i : Nat} (h : sat t p i) :
    sat t (.eventually p) i := ⟨i, Nat.le_refl i, h⟩

/-- Weak until holds vacuously when `q` fires immediately: no tick lies
strictly before the first `q`. -/
theorem sat_until_of_q_now {p q : Prop' D} {i : Nat} (h : sat t q i) :
    sat t (.until' p q) i := by
  intro j hij hq
  exact absurd h (hq i (Nat.le_refl i) hij)

/-- Weak until against the never-true property is `always` — the
"if `q` never holds, `p` must hold forever" reading of weakness. -/
theorem sat_until_ff_iff (p : Prop' D) (i : Nat) :
    sat t (.until' p .ff) i ↔ sat t (.always p) i := by
  have hff : ∀ k, ¬ sat t Prop'.ff k := by
    rintro k ⟨len, _, h⟩
    simp at h
  constructor
  · intro h j hj
    exact h j hj fun k _ _ => hff k
  · intro h j hj _
    exact h j hj

/-- `holds` distributes over conjunction. -/
theorem holds_and_iff (p q : Prop' D) :
    holds D (.and p q) ↔ holds D p ∧ holds D q := by
  constructor
  · intro h
    exact ⟨fun tr hv => (h tr hv).1, fun tr hv => (h tr hv).2⟩
  · rintro ⟨hp, hq⟩ tr hv
    exact ⟨hp tr hv, hq tr hv⟩

/-- The trivially-true property holds of every design. -/
theorem holds_always_tt (D : Design) : holds D (.always .tt) := by
  intro tr _ j _
  exact ⟨1, rfl, rfl⟩

end Lemmas

end Veda
