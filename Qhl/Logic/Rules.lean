import Qhl.Logic.Assertion

/-!
# L-2 / L-3: the proof systems `QHL⁺_par` and `QHL⁺_tot`

Subgoals L-2 and L-3 of spec 07 (paper arXiv:2412.09869 Tables 2 and 3).

`DerivPar` and `DerivTot` formalize semantic rule instances and explicit
extensions of the source systems. Measurement uses the summed transformer
(Rule-Meas-sum); `Qhl.Logic.MeasurementSource` derives the source per-outcome
(Axiom-Meas), but the general accumulation rules are not formalized.
`DerivTot` includes Table 3's total-loop rule as `whileLoopSource` and also
retains the combined-premise extension `whileLoop`. Both are proved sound,
but their premises are not equivalent. Derivations are `Prop`-valued;
soundness is proved by induction.

Representation choices and extensions:

* **V1** the syntactic pair `(φ, A)` is represented by a masked effect
  family. `mask_le_mask` embeds source cq-entailment in masked Löwner order;
  the converse does not hold, since zero effects can hide a failed classical
  implication. `guard_mask_guard` recovers the source conditional instance.
* **V3** measurement uses a summed transformer rather than the source's
  fresh-variable axiom. The source total-loop rule quantifies over an
  immutable integer ranking value directly.
* **V7** where `Dist(q̄)` fails the precondition is `0`, matching the paper's
  "undefined ⇒ the triple says nothing there".
-/

namespace Qhl

open Finset
open scoped NNReal ENNReal ComplexOrder

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## L-2: `QHL⁺_par` (paper Table 2) -/

/-- L-2: derivability in the partial-correctness system of paper Table 2. -/
inductive DerivPar : Assn σT D → Prog σT D → Assn σT D → Prop
  /-- (Ax-Ski). -/
  | skip (A : Assn σT D) : DerivPar A .skip A
  /-- (Ax-Ass): `{A[e/x]} x := e {A}`. -/
  | assign (f : σT → σT) (A : Assn σT D) : DerivPar (A.comp f) (.assign f) A
  /-- (Ax-Init): the precondition is `E†(A)` for the initialisation channel. -/
  | initProg (S : σT → Finset L) (A : Assn σT D) : DerivPar (A.initPre S) (.init S) A
  /-- (Ax-Uni): the precondition is `U†AU`. -/
  | unitary {k : ℕ} (r : RegExpr σT L k) (U : ∀ σ, UnitaryOp (TSpace D (r σ)))
      (A : Assn σT D) : DerivPar (A.unitaryPre r U) (.unitary k r U) A
  /-- (Ax-Meas) in Born-sum form (V3). -/
  | measure {m k : ℕ} (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
      (upd : Fin m → σT → σT) (A : Assn σT D) :
      DerivPar (A.measurePre r M upd) (.measure m k r M upd) A
  /-- (R-Seq). -/
  | seq {A B C : Assn σT D} {P₁ P₂ : Prog σT D} :
      DerivPar A P₁ B → DerivPar B P₂ C → DerivPar A (P₁.seq P₂) C
  /-- (R-Cond), in the `guard` form (strictly more general than the paper's). -/
  | cond {b : σT → Bool} {A₁ A₀ B : Assn σT D} {P₁ P₀ : Prog σT D} :
      DerivPar A₁ P₁ B → DerivPar A₀ P₀ B →
      DerivPar (Assn.guard b A₁ A₀) (.ite b P₁ P₀) B
  /-- (R-Loop-par). -/
  | whileLoop {b : σT → Bool} {J : Assn σT D} {P : Prog σT D} :
      DerivPar (J.mand b) P J → DerivPar J (.while b P) (J.mandNot b)
  /-- (R-Conseq). -/
  | conseq {A A' B' B : Assn σT D} {P : Prog σT D} :
      A ≤ A' → DerivPar A' P B' → B' ≤ B → DerivPar A P B

/-! ## L-2: `QHL⁺_tot` (paper Table 3) -/

/-- Total-correctness derivability, including the source total-loop rule and
the explicitly separate combined-premise loop extension. -/
inductive DerivTot : Assn σT D → Prog σT D → Assn σT D → Prop
  /-- (Ax-Ski). -/
  | skip (A : Assn σT D) : DerivTot A .skip A
  /-- (Ax-Ass). -/
  | assign (f : σT → σT) (A : Assn σT D) : DerivTot (A.comp f) (.assign f) A
  /-- (Ax-Init). -/
  | initProg (S : σT → Finset L) (A : Assn σT D) : DerivTot (A.initPre S) (.init S) A
  /-- (Ax-Uni). -/
  | unitary {k : ℕ} (r : RegExpr σT L k) (U : ∀ σ, UnitaryOp (TSpace D (r σ)))
      (A : Assn σT D) : DerivTot (A.unitaryPre r U) (.unitary k r U) A
  /-- (Ax-Meas). -/
  | measure {m k : ℕ} (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
      (upd : Fin m → σT → σT) (A : Assn σT D) :
      DerivTot (A.measurePre r M upd) (.measure m k r M upd) A
  /-- (R-Seq). -/
  | seq {A B C : Assn σT D} {P₁ P₂ : Prog σT D} :
      DerivTot A P₁ B → DerivTot B P₂ C → DerivTot A (P₁.seq P₂) C
  /-- (R-Cond). -/
  | cond {b : σT → Bool} {A₁ A₀ B : Assn σT D} {P₁ P₀ : Prog σT D} :
      DerivTot A₁ P₁ B → DerivTot A₀ P₀ B →
      DerivTot (Assn.guard b A₁ A₀) (.ite b P₁ P₀) B
  /-- Combined-premise total-loop extension: decrease is weighted by `J`.
  This does not require the source rule's independent identity-predicate
  decrease premise. Use `whileLoopSource` for the printed (R-Loop-tot). -/
  | whileLoop {b : σT → Bool} {J : Assn σT D} {P : Prog σT D} (t : σT → ℕ) :
      (∀ n : ℕ, DerivTot ((J.mand b).mask fun σ => t σ = n) P
        (J.mask fun σ => t σ < n)) →
      DerivTot J (.while b P) (J.mandNot b)
  /-- The printed (R-Loop-tot): invariant preservation, independent decrease
  with the identity quantum predicate, and an integer rank nonnegative under
  the classical invariant. The outer integer parameter is immutable. -/
  | whileLoopSource {b : σT → Bool} {A : Assn σT D} {φ : σT → Prop}
      {P : Prog σT D} (t : σT → Int) (hbound : ∀ σ, φ σ → 0 ≤ t σ) :
      DerivTot ((A.mask φ).mand b) P (A.mask φ) →
      (∀ z : Int, DerivTot
        ((Assn.one : Assn σT D).mask fun σ => φ σ ∧ b σ = true ∧ t σ = z)
        P ((Assn.one : Assn σT D).mask fun σ => t σ < z)) →
      DerivTot (A.mask φ) (.while b P) ((A.mask φ).mandNot b)
  /-- (R-Conseq). -/
  | conseq {A A' B' B : Assn σT D} {P : Prog σT D} :
      A ≤ A' → DerivTot A' P B' → B' ≤ B → DerivTot A P B

/-! ## L-3: the paper-shaped corollaries -/

namespace Assn

/-- L-3: masking is monotone in both components — the paper's cq-entailment
`(φ, A) ⊨ (ψ, B)` of Def 4.8, in the form (R-Conseq) consumes. -/
theorem mask_le_mask {A B : Assn σT D} {φ ψ : σT → Prop}
    (hφψ : ∀ σ, φ σ → ψ σ) (hAB : ∀ σ, φ σ → A.op σ ≤ B.op σ) :
    A.mask φ ≤ B.mask ψ := by
  intro σ
  by_cases h : φ σ
  · rw [mask_op_of_pos h, mask_op_of_pos (hφψ σ h)]
    exact hAB σ h
  · rw [mask_op_of_neg h]
    exact ((B.mask ψ).isEffect σ).1

/-- L-3: the paper's (R-Cond) strengthens only the classical component; that
instance of the `guard` combinator collapses back to a single mask. -/
theorem guard_mask_guard (b : σT → Bool) (A : Assn σT D) (φ : σT → Prop) :
    Assn.guard b (A.mask fun σ => φ σ ∧ b σ = true)
        (A.mask fun σ => φ σ ∧ b σ = false)
      = A.mask φ := by
  ext σ
  by_cases hb : b σ = true
  · rw [guard_op_of_true hb]
    by_cases h : φ σ
    · rw [mask_op_of_pos ⟨h, hb⟩, mask_op_of_pos h]
    · rw [mask_op_of_neg fun hc => h hc.1, mask_op_of_neg h]
  · rw [Bool.not_eq_true] at hb
    rw [guard_op_of_false hb]
    by_cases h : φ σ
    · rw [mask_op_of_pos ⟨h, hb⟩, mask_op_of_pos h]
    · rw [mask_op_of_neg fun hc => h hc.1, mask_op_of_neg h]

end Assn

/-- L-3: the paper's (R-Cond) verbatim — the classical precondition `φ` is
strengthened by the guard in each branch. -/
theorem DerivPar.cond' {b : σT → Bool} {A B : Assn σT D} {φ : σT → Prop}
    {P₁ P₀ : Prog σT D}
    (h₁ : DerivPar (A.mask fun σ => φ σ ∧ b σ = true) P₁ B)
    (h₀ : DerivPar (A.mask fun σ => φ σ ∧ b σ = false) P₀ B) :
    DerivPar (A.mask φ) (.ite b P₁ P₀) B :=
  Assn.guard_mask_guard b A φ ▸ DerivPar.cond h₁ h₀

/-- L-3: the paper's (R-Cond) verbatim, total version. -/
theorem DerivTot.cond' {b : σT → Bool} {A B : Assn σT D} {φ : σT → Prop}
    {P₁ P₀ : Prog σT D}
    (h₁ : DerivTot (A.mask fun σ => φ σ ∧ b σ = true) P₁ B)
    (h₀ : DerivTot (A.mask fun σ => φ σ ∧ b σ = false) P₀ B) :
    DerivTot (A.mask φ) (.ite b P₁ P₀) B :=
  Assn.guard_mask_guard b A φ ▸ DerivTot.cond h₁ h₀

/-- L-3: the paper's (R-Loop-par) with the invariant printed as a pair
`(φ, A)` — `J := A.mask φ`. -/
theorem DerivPar.whileLoop' {b : σT → Bool} {A : Assn σT D} {φ : σT → Prop}
    {P : Prog σT D}
    (h : DerivPar ((A.mask φ).mand b) P (A.mask φ)) :
    DerivPar (A.mask φ) (.while b P) ((A.mask φ).mandNot b) :=
  DerivPar.whileLoop h

/-- Combined-premise loop extension with an explicitly masked invariant.
This is not the separate-premise rule `DerivTot.whileLoopSource`. -/
theorem DerivTot.whileLoop' {b : σT → Bool} {A : Assn σT D} {φ : σT → Prop}
    {P : Prog σT D} (t : σT → ℕ)
    (h : ∀ n : ℕ, DerivTot (((A.mask φ).mand b).mask fun σ => t σ = n) P
      ((A.mask φ).mask fun σ => t σ < n)) :
    DerivTot (A.mask φ) (.while b P) ((A.mask φ).mandNot b) :=
  DerivTot.whileLoop t h

end Qhl
