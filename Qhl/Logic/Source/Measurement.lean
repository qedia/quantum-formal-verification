import Qhl.Logic.Source.Assertion
import Qhl.Logic.MeasurementSource

/-! # Per-outcome measurement with explicit classical conditions and definedness -/

namespace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

namespace SourceAssertion

/-- The single-outcome source precondition. The source domain explicitly requires
register distinctness and definedness of the post quantum formula after update. -/
noncomputable def measureOutcomePreSource (A : SourceAssertion σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) (y : σT → Fin m) : SourceAssertion σT D where
  classical σ := A.classical (upd (y σ) σ)
  defined σ := Function.Injective (r σ) ∧ A.defined (upd (y σ) σ)
  quantum := A.quantum.measureOutcomePre r M upd y

/-- The source postcondition conjoins the read outcome with the ghost value. -/
noncomputable def measureOutcomePostSource (A : SourceAssertion σT D) {m : ℕ}
    (x y : σT → Fin m) : SourceAssertion σT D where
  classical σ := A.classical σ ∧ x σ = y σ
  defined := A.defined
  quantum := A.quantum

/-- Interpreting the explicit source postcondition combines its classical and
definedness masks. -/
theorem measureOutcomePostSource_toAssn (A : SourceAssertion σT D) {m : ℕ}
    (x y : σT → Fin m) :
    (A.measureOutcomePostSource x y).toAssn =
      (A.quantum.mask A.defined).mask (fun σ => A.classical σ ∧ x σ = y σ) := by
  apply Assn.ext
  funext σ
  simp only [measureOutcomePostSource, SourceAssertion.toAssn]
  by_cases hc : A.classical σ ∧ x σ = y σ
  · by_cases hd : A.defined σ
    · rw [Assn.mask_op_of_pos ⟨hc, hd⟩,
        Assn.mask_op_of_pos (φ := fun τ => A.classical τ ∧ x τ = y τ) hc,
        Assn.mask_op_of_pos (φ := A.defined) hd]
    · rw [Assn.mask_op_of_neg (fun h => hd h.2),
        Assn.mask_op_of_pos (φ := fun τ => A.classical τ ∧ x τ = y τ) hc,
        Assn.mask_op_of_neg (φ := A.defined) hd]
  · rw [Assn.mask_op_of_neg (fun h => hc h.1),
      Assn.mask_op_of_neg (φ := fun τ => A.classical τ ∧ x τ = y τ) hc]

/-- The explicit source precondition has the same effect as the already-proved
single-outcome transformer applied to the post quantum formula on its domain. -/
theorem measureOutcomePreSource_toAssn (A : SourceAssertion σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) (y : σT → Fin m) :
    (A.measureOutcomePreSource r M upd y).toAssn =
      ((A.quantum.mask A.defined).measureOutcomePre r M upd y).mask
        (fun σ => A.classical (upd (y σ) σ)) := by
  apply Assn.ext
  funext σ
  simp only [measureOutcomePreSource, SourceAssertion.toAssn]
  by_cases hc : A.classical (upd (y σ) σ)
  · by_cases hi : Function.Injective (r σ)
    · by_cases hd : A.defined (upd (y σ) σ)
      · rw [Assn.mask_op_of_pos ⟨hc, hi, hd⟩,
          Assn.mask_op_of_pos (φ := fun τ => A.classical (upd (y τ) τ)) hc]
        simp only [Assn.measureOutcomePre, dif_pos hi]
        rw [Assn.mask_op_of_pos (φ := A.defined) hd]
      · rw [Assn.mask_op_of_neg (fun h => hd h.2.2),
          Assn.mask_op_of_pos (φ := fun τ => A.classical (upd (y τ) τ)) hc]
        simp only [Assn.measureOutcomePre, dif_pos hi]
        rw [Assn.mask_op_of_neg (φ := A.defined) hd]
        simp
    · rw [Assn.mask_op_of_neg (fun h => hi h.2.1),
        Assn.mask_op_of_pos (φ := fun τ => A.classical (upd (y τ) τ)) hc]
      simp only [Assn.measureOutcomePre, dif_neg hi]
  · rw [Assn.mask_op_of_neg (fun h => hc h.1),
      Assn.mask_op_of_neg (φ := fun τ => A.classical (upd (y τ) τ)) hc]

/-- Generalized source-level partial measurement rule with explicit
read-after-write and ghost-preservation hypotheses. -/
theorem measureOutcomeSourcePar (A : SourceAssertion σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) (x y : σT → Fin m)
    (hwrite : ∀ i σ, x (upd i σ) = i)
    (hfresh : ∀ i σ, y (upd i σ) = y σ) :
    DerivPar (A.measureOutcomePreSource r M upd y).toAssn
      (.measure m k r M upd) (A.measureOutcomePostSource x y).toAssn := by
  rw [measureOutcomePreSource_toAssn, measureOutcomePostSource_toAssn]
  exact DerivPar.measureSource r M upd x y hwrite hfresh
    (A.quantum.mask A.defined) A.classical

/-- Total-correctness version of the generalized source measurement rule. -/
theorem measureOutcomeSourceTot (A : SourceAssertion σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) (x y : σT → Fin m)
    (hwrite : ∀ i σ, x (upd i σ) = i)
    (hfresh : ∀ i σ, y (upd i σ) = y σ) :
    DerivTot (A.measureOutcomePreSource r M upd y).toAssn
      (.measure m k r M upd) (A.measureOutcomePostSource x y).toAssn := by
  rw [measureOutcomePreSource_toAssn, measureOutcomePostSource_toAssn]
  exact DerivTot.measureSource r M upd x y hwrite hfresh
    (A.quantum.mask A.defined) A.classical

#print axioms measureOutcomeSourcePar
#print axioms measureOutcomeSourceTot

end SourceAssertion
end Qhl
