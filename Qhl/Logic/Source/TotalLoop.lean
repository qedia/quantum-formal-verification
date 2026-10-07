import Qhl.Logic.Source.Consequence

/-! # The source total-loop rule for explicit classical-quantum assertions -/

namespace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

namespace SourceAssertion

/-- Replace only the classical formula, keeping the quantum formula and its
domain unchanged. -/
def withClassical (A : SourceAssertion σT D) (φ : σT → Prop) :
    SourceAssertion σT D := { A with classical := φ }

/-- The source identity quantum predicate, defined at every classical state. -/
def identity (φ : σT → Prop) : SourceAssertion σT D where
  classical := φ
  defined := fun _ => True
  quantum := Assn.one

/-- The source identity predicate interprets as the usual masked identity. -/
theorem identity_toAssn (φ : σT → Prop) :
    (identity (D := D) φ).toAssn = (Assn.one : Assn σT D).mask φ := by
  apply Assn.ext
  funext σ
  change ((Assn.one : Assn σT D).mask (fun τ => φ τ ∧ True)).op σ =
    ((Assn.one : Assn σT D).mask φ).op σ
  by_cases hφ : φ σ
  · rw [Assn.mask_op_of_pos hφ, Assn.mask_op_of_pos ⟨hφ, trivial⟩]
  · rw [Assn.mask_op_of_neg hφ,
      Assn.mask_op_of_neg (fun h => hφ h.1)]

/-- Guarded source assertions agree with the backend's nested masks. -/
theorem guard_toAssn (A : SourceAssertion σT D) (b : σT → Bool) :
    (A.withClassical fun σ => A.classical σ ∧ b σ = true).toAssn =
      ((A.quantum.mask A.defined).mask A.classical).mand b := by
  apply Assn.ext
  funext σ
  by_cases hc : A.classical σ
  · by_cases hd : A.defined σ
    · by_cases hb : b σ = true
      · simp [toAssn, withClassical, Assn.mand, Assn.mask, hc, hd, hb]
      · simp [toAssn, withClassical, Assn.mand, Assn.mask, hc, hd, hb]
    · simp [toAssn, withClassical, Assn.mand, Assn.mask, hc, hd]
  · simp [toAssn, withClassical, Assn.mand, Assn.mask, hc]

/-- Exit source assertions agree with the backend's negated-guard mask. -/
theorem exit_toAssn (A : SourceAssertion σT D) (b : σT → Bool) :
    (A.withClassical fun σ => A.classical σ ∧ b σ = false).toAssn =
      ((A.quantum.mask A.defined).mask A.classical).mandNot b := by
  apply Assn.ext
  funext σ
  by_cases hc : A.classical σ
  · by_cases hd : A.defined σ
    · by_cases hb : b σ = false
      · simp [toAssn, withClassical, Assn.mandNot, Assn.mask, hc, hd, hb]
      · simp [toAssn, withClassical, Assn.mandNot, Assn.mask, hc, hd, hb]
    · simp [toAssn, withClassical, Assn.mandNot, Assn.mask, hc, hd]
  · simp [toAssn, withClassical, Assn.mandNot, Assn.mask, hc]

/-- The definedness mask is associative with the classical mask. -/
theorem toAssn_eq_nested_mask (A : SourceAssertion σT D) :
    A.toAssn = (A.quantum.mask A.defined).mask A.classical := by
  apply Assn.ext
  funext σ
  by_cases hc : A.classical σ
  · by_cases hd : A.defined σ
    · simp [toAssn, Assn.mask, hc, hd]
    · simp [toAssn, Assn.mask, hc, hd]
  · simp [toAssn, Assn.mask, hc]

end SourceAssertion

/-- The original total-loop rule transported to explicit source assertions.
The outer integer `z` is an immutable quantified parameter representing the
paper's fresh ghost value; this theorem does not formalize ghost-variable syntax.
The rank premise uses the everywhere-defined identity quantum predicate. -/
theorem DerivTot.sourceWhile {A : SourceAssertion σT D} {b : σT → Bool}
    {P : Prog σT D} (t : σT → Int)
    (hbound : ∀ σ, A.classical σ → 0 ≤ t σ)
    (hInv : DerivTot
      (A.withClassical fun σ => A.classical σ ∧ b σ = true).toAssn P A.toAssn)
    (hRank : ∀ z : Int, DerivTot
      (SourceAssertion.identity (D := D)
        (fun σ => A.classical σ ∧ b σ = true ∧ t σ = z)).toAssn P
      (SourceAssertion.identity (D := D) (fun σ => t σ < z)).toAssn) :
    DerivTot A.toAssn (.while b P)
      (A.withClassical fun σ => A.classical σ ∧ b σ = false).toAssn := by
  have hBase := DerivTot.whileLoopSource (A := A.quantum.mask A.defined)
    (φ := A.classical) (b := b) (P := P) t hbound
  rw [SourceAssertion.guard_toAssn, SourceAssertion.toAssn_eq_nested_mask] at hInv
  have hRank' : ∀ z : Int, DerivTot
      ((Assn.one : Assn σT D).mask
        fun σ => A.classical σ ∧ b σ = true ∧ t σ = z) P
      ((Assn.one : Assn σT D).mask fun σ => t σ < z) := by
    intro z
    simpa only [SourceAssertion.identity_toAssn] using hRank z
  have h := hBase hInv hRank'
  rw [SourceAssertion.toAssn_eq_nested_mask, SourceAssertion.exit_toAssn]
  exact h

/-- Semantic total correctness of the source total-loop instance follows
from soundness of the existing total derivation. -/
theorem validTot_sourceWhile {A : SourceAssertion σT D} {b : σT → Bool}
    {P : Prog σT D} (t : σT → Int)
    (hbound : ∀ σ, A.classical σ → 0 ≤ t σ)
    (hInv : DerivTot
      (A.withClassical fun σ => A.classical σ ∧ b σ = true).toAssn P A.toAssn)
    (hRank : ∀ z : Int, DerivTot
      (SourceAssertion.identity (D := D)
        (fun σ => A.classical σ ∧ b σ = true ∧ t σ = z)).toAssn P
      (SourceAssertion.identity (D := D) (fun σ => t σ < z)).toAssn) :
    validTot A.toAssn (.while b P)
      (A.withClassical fun σ => A.classical σ ∧ b σ = false).toAssn :=
  (DerivTot.sourceWhile t hbound hInv hRank).sound

end Qhl
