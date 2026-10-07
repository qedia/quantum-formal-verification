import Qhl.Logic.Source.MeasurementSelected
import Qhl.Logic.Source.Mask

/-! # All-outcome measurement with strict operand definedness -/
namespace Qhl
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}
namespace SourceAssertion
/-- The all-outcome axiom requires every substituted operand to be defined,
including operands of zero measurement operators. -/
noncomputable def measureAllPreSource (A : SourceAssertion σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) : SourceAssertion σT D where
  classical σ := ∀ i, A.classical (upd i σ)
  defined σ := Function.Injective (r σ) ∧ ∀ i, A.defined (upd i σ)
  quantum := A.quantum.measurePre r M upd

/-- The interpreted all-outcome precondition is below the semantic transformer. -/
theorem measureAllPreSource_le (A : SourceAssertion σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) :
    (A.measureAllPreSource r M upd).toAssn ≤ A.toAssn.measurePre r M upd := by
  intro σ
  by_cases h : (A.measureAllPreSource r M upd).classical σ ∧
      (A.measureAllPreSource r M upd).defined σ
  · rw [toAssn, Assn.mask_op_of_pos (φ := fun τ =>
      (A.measureAllPreSource r M upd).classical τ ∧
      (A.measureAllPreSource r M upd).defined τ) h]
    change (A.quantum.measurePre r M upd).op σ ≤ _
    rw [Assn.measurePre_op_of_dist _ r M upd h.2.1,
      Assn.measurePre_op_of_dist _ r M upd h.2.1]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i _
    rw [toAssn, Assn.mask_op_of_pos (φ := fun τ => A.classical τ ∧ A.defined τ) ⟨h.1 i, h.2.2 i⟩]
  · rw [toAssn, Assn.mask_op_of_neg (φ := fun τ =>
      (A.measureAllPreSource r M upd).classical τ ∧
      (A.measureAllPreSource r M upd).defined τ) h]
    exact ((A.toAssn.measurePre r M upd).isEffect σ).1

/-- Postpredicate used to derive selected outcomes from all outcomes and masking. -/
noncomputable def measureSelectionOperand (A : SourceAssertion σT D) {m : ℕ}
    (x : σT → Fin m) (S : σT → Fin m → Bool) : SourceAssertion σT D :=
  (A.withClassical fun σ => S σ (x σ) = true → A.classical σ).quantumMask
    (fun σ => S σ (x σ) = true)

/-- Selected and all-outcome preconditions agree when the omitted operands
are also defined on the selected precondition's domain. -/
theorem measureSelectedPreSource_all (A : SourceAssertion σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (x : SourceVariable σT (Fin m)) (S : σT → Fin m → Bool)
    (hS : ∀ i σ, S (x.set i σ) = S σ)
    (hdom : ∀ σ, (A.measureSelectedPreSource r M x.set S).classical σ →
      (∀ i, S σ i = true → A.defined (x.set i σ)) → ∀ i, A.defined (x.set i σ)) :
    Entails (A.measureSelectedPreSource r M x.set S)
      ((A.measureSelectionOperand x.get S).measureAllPreSource r M x.set) := by
  constructor
  · intro σ hc i hi
    apply hc i
    simpa only [hS, x.get_set] using hi
  · intro σ hc
    constructor
    · change (Function.Injective (r σ) ∧ ∀ i, S σ i = true → A.defined (x.set i σ)) ↔
        (Function.Injective (r σ) ∧ ∀ i, A.defined (x.set i σ))
      exact ⟨fun hd => ⟨hd.1, hdom σ hc hd.2⟩,
        fun hd => ⟨hd.1, fun i _ => hd.2 i⟩⟩
    · intro hd
      apply le_of_eq
      change (if h : Function.Injective (r σ) then _ else 0) =
        ((A.measureSelectionOperand x.get S).quantum.measurePre r M x.set).op σ
      rw [dif_pos hd.1, Assn.measurePre_op_of_dist _ r M x.set hd.1]
      apply Finset.sum_congr rfl
      intro i _
      simp only [measureSelectionOperand, quantumMask, withClassical, Assn.mask,
        hS, x.get_set]

/-- The classical result of Rule-Mask entails the selected postcondition. -/
theorem measureSelectionOperand_post (A : SourceAssertion σT D) {m : ℕ}
    (x : σT → Fin m) (S : σT → Fin m → Bool) :
    Entails
      ((A.withClassical fun σ => S σ (x σ) = true → A.classical σ).withClassical
        fun σ => (S σ (x σ) = true → A.classical σ) ∧ S σ (x σ) = true)
      (A.measureSelectedPostSource x S) := by
  constructor
  · intro σ h
    exact ⟨h.1 h.2, h.2⟩
  · intro σ _
    exact ⟨Iff.rfl, fun _ => le_rfl⟩
end SourceAssertion
end Qhl
