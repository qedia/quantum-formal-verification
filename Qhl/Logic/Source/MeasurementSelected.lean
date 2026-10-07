import Qhl.Logic.Source.Measurement
import Qhl.Logic.Source.Variable

/-! # Selected-outcome measurement with explicit operand domains -/

namespace Qhl

open scoped ComplexOrder

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

namespace SourceAssertion

/-- The selected Born sum, requiring every selected operand to be defined, including
operands whose Kraus operator is zero. -/
noncomputable def measureSelectedPreSource (A : SourceAssertion σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) (S : σT → Fin m → Bool) : SourceAssertion σT D where
  classical σ := ∀ i, S σ i = true → A.classical (upd i σ)
  defined σ := Function.Injective (r σ) ∧ ∀ i, S σ i = true → A.defined (upd i σ)
  quantum := {
    op σ := if h : Function.Injective (r σ) then
      ∑ i, LinearMap.adjoint (regLift ⟨r σ, h⟩ ((M σ).M i)) ∘ₗ
        (if S σ i = true then A.quantum.op (upd i σ) else 0) ∘ₗ
        regLift ⟨r σ, h⟩ ((M σ).M i)
      else 0
    isEffect σ := by
      classical
      split_ifs with h
      · apply isEffect_sum_conj _ (isQMeasure_regLift ⟨r σ, h⟩ (M σ))
        intro i
        split_ifs
        · exact A.quantum.isEffect _
        · exact isEffect_zero
      · exact isEffect_zero }

/-- The measured value satisfies the selector; the original quantum domain is retained. -/
noncomputable def measureSelectedPostSource (A : SourceAssertion σT D) {m : ℕ}
    (x : σT → Fin m) (S : σT → Fin m → Bool) : SourceAssertion σT D where
  classical σ := A.classical σ ∧ S σ (x σ) = true
  defined := A.defined
  quantum := A.quantum

/-- On the source precondition's classical and quantum domain, the selected sum
is the complete measurement transformer of the interpreted selected postcondition. -/
theorem measureSelectedPreSource_op (A : SourceAssertion σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (x : SourceVariable σT (Fin m)) (S : σT → Fin m → Bool)
    (hS : ∀ i σ, S (x.set i σ) = S σ) (σ : σT)
    (hc : (A.measureSelectedPreSource r M x.set S).classical σ)
    (hd : (A.measureSelectedPreSource r M x.set S).defined σ) :
    (A.measureSelectedPreSource r M x.set S).quantum.op σ =
      ((A.measureSelectedPostSource x.get S).toAssn.measurePre r M x.set).op σ := by
  classical
  rw [Assn.measurePre_op_of_dist _ r M x.set hd.1]
  change (if h : Function.Injective (r σ) then _ else 0) = _
  rw [dif_pos hd.1]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : S σ i = true
  · rw [if_pos hi]
    have hp : (A.measureSelectedPostSource x.get S).classical (x.set i σ) ∧
        (A.measureSelectedPostSource x.get S).defined (x.set i σ) :=
      ⟨⟨hc i hi, by simpa only [hS, x.get_set] using hi⟩, hd.2 i hi⟩
    rw [toAssn, Assn.mask_op_of_pos (φ := fun τ =>
      (A.measureSelectedPostSource x.get S).classical τ ∧
      (A.measureSelectedPostSource x.get S).defined τ) hp]
    rfl
  · rw [if_neg hi, toAssn, Assn.mask_op_of_neg (φ := fun τ =>
      (A.measureSelectedPostSource x.get S).classical τ ∧
      (A.measureSelectedPostSource x.get S).defined τ) (by
      intro hp
      exact hi (by simpa only [measureSelectedPostSource, hS, x.get_set] using hp.1.2))]

/-- The source mask may remove additional states; consequently the semantic
comparison is one-sided, rather than an unconditional transformer equality. -/
theorem measureSelectedPreSource_le (A : SourceAssertion σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (x : SourceVariable σT (Fin m)) (S : σT → Fin m → Bool)
    (hS : ∀ i σ, S (x.set i σ) = S σ) :
    (A.measureSelectedPreSource r M x.set S).toAssn ≤
      (A.measureSelectedPostSource x.get S).toAssn.measurePre r M x.set := by
  intro σ
  by_cases h : (A.measureSelectedPreSource r M x.set S).classical σ ∧
      (A.measureSelectedPreSource r M x.set S).defined σ
  · rw [toAssn, Assn.mask_op_of_pos (φ := fun τ =>
      (A.measureSelectedPreSource r M x.set S).classical τ ∧
      (A.measureSelectedPreSource r M x.set S).defined τ) h,
      measureSelectedPreSource_op A r M x S hS σ h.1 h.2]
  · rw [toAssn, Assn.mask_op_of_neg (φ := fun τ =>
      (A.measureSelectedPreSource r M x.set S).classical τ ∧
      (A.measureSelectedPreSource r M x.set S).defined τ) h]
    exact (((A.measureSelectedPostSource x.get S).toAssn.measurePre r M x.set).isEffect σ).1

/-- Partial correctness of selected-outcome measurement. -/
theorem measureSelectedSourcePar (A : SourceAssertion σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (x : SourceVariable σT (Fin m)) (S : σT → Fin m → Bool)
    (hS : ∀ i σ, S (x.set i σ) = S σ) :
    DerivPar (A.measureSelectedPreSource r M x.set S).toAssn
      (.measure m k r M x.set) (A.measureSelectedPostSource x.get S).toAssn :=
  .conseq (measureSelectedPreSource_le A r M x S hS) (.measure r M x.set _) (fun _ => le_rfl)

/-- Total correctness of selected-outcome measurement. -/
theorem measureSelectedSourceTot (A : SourceAssertion σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (x : SourceVariable σT (Fin m)) (S : σT → Fin m → Bool)
    (hS : ∀ i σ, S (x.set i σ) = S σ) :
    DerivTot (A.measureSelectedPreSource r M x.set S).toAssn
      (.measure m k r M x.set) (A.measureSelectedPostSource x.get S).toAssn :=
  .conseq (measureSelectedPreSource_le A r M x S hS) (.measure r M x.set _) (fun _ => le_rfl)

/-- Singleton selection recovers the original source assertion, including its domain. -/
theorem measureSelectedPreSource_singleton (A : SourceAssertion σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) (y : σT → Fin m) :
    Eqv (A.measureOutcomePreSource r M upd y)
      (A.measureSelectedPreSource r M upd (fun σ i => decide (i = y σ))) := by
  classical
  apply (eqv_iff _ _).mpr
  constructor
  · intro σ
    simp [measureOutcomePreSource, measureSelectedPreSource]
  · intro σ _
    constructor
    · simp [measureOutcomePreSource, measureSelectedPreSource]
    · intro hd
      have hi := hd.1
      change (if h : Function.Injective (r σ) then _ else 0) =
        (if h : Function.Injective (r σ) then _ else 0)
      rw [dif_pos hi, dif_pos hi]
      symm
      rw [Finset.sum_eq_single (y σ)]
      · simp
      · intro i _ hne
        simp [hne]
      · simp

/-- Singleton selection also recovers the original classical postcondition. -/
theorem measureSelectedPostSource_singleton (A : SourceAssertion σT D) {m : ℕ}
    (x y : σT → Fin m) :
    Eqv (A.measureSelectedPostSource x (fun σ i => decide (i = y σ)))
      (A.measureOutcomePostSource x y) := by
  apply (eqv_iff _ _).mpr
  constructor
  · intro σ
    simp [measureSelectedPostSource, measureOutcomePostSource]
  · intro σ _
    exact ⟨Iff.rfl, fun _ => rfl⟩

end SourceAssertion
end Qhl
