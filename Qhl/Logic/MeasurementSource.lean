import Qhl.Logic.Rules

/-!
# The source per-outcome measurement rule

The summed measurement constructor admits a generalized single-outcome
semantic instance. Read-after-write for the outcome and preservation of the
ghost value are explicit hypotheses. To obtain the source (Axiom-Meas),
specialize the update to ordinary assignment to `x` alone and choose `y`
fresh for the assertions and `x`. The semantic hypotheses alone do not
express that syntactic freshness. This does not assert the reverse
translation, or recover the source accumulation rules.
-/

namespace Qhl

open Finset
open scoped ComplexOrder

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

namespace Assn

/-- One summand of a normalized measurement is a contraction. -/
theorem measurement_kraus_le_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {m : ℕ} (K : Fin m → E →ₗ[ℂ] E)
    (hK : ∑ i, LinearMap.adjoint (K i) ∘ₗ K i = 1) (i : Fin m) :
    LinearMap.adjoint (K i) ∘ₗ K i ≤ 1 := by
  rw [← hK]
  apply Finset.single_le_sum (f := fun j => LinearMap.adjoint (K j) ∘ₗ K j) (s := Finset.univ)
  · intro j _
    exact (LinearMap.nonneg_iff_isPositive _).mpr (by
      simpa only [Module.End.one_eq_id, LinearMap.id_comp] using
        (show IsEffect (1 : E →ₗ[ℂ] E) from isEffect_one).isPositive.adjoint_conj (K j))
  · exact Finset.mem_univ i

/-- The source single-outcome precondition. The register and Kraus operator
are evaluated before the update; the postcondition is evaluated afterwards.
Failed register distinctness gives zero, as for `measurePre`. -/
noncomputable def measureOutcomePre (A : Assn σT D) {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) (y : σT → Fin m) : Assn σT D where
  op σ := if h : Function.Injective (r σ) then
      LinearMap.adjoint (regLift ⟨r σ, h⟩ ((M σ).M (y σ)))
        ∘ₗ A.op (upd (y σ) σ) ∘ₗ regLift ⟨r σ, h⟩ ((M σ).M (y σ))
    else 0
  isEffect σ := by
    split_ifs with h
    · exact isEffect_conj (A.isEffect _) (measurement_kraus_le_one _
        (isQMeasure_regLift ⟨r σ, h⟩ (M σ)) (y σ))
    · exact isEffect_zero

/-- Selecting the postcondition `φ ∧ x = y` collapses the summed transformer
to the single outcome read from the unchanged ghost variable `y`. -/
theorem measurePre_mask_eq_measureOutcomePre {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) (x y : σT → Fin m)
    (hwrite : ∀ i σ, x (upd i σ) = i)
    (hfresh : ∀ i σ, y (upd i σ) = y σ)
    (A : Assn σT D) (φ : σT → Prop) :
    (A.mask (fun σ => φ σ ∧ x σ = y σ)).measurePre r M upd =
      (A.measureOutcomePre r M upd y).mask (fun σ => φ (upd (y σ) σ)) := by
  classical
  apply Assn.ext
  funext σ
  by_cases hd : Function.Injective (r σ)
  · rw [measurePre_op_of_dist _ r M upd hd]
    rw [Finset.sum_eq_single (y σ)]
    · by_cases hp : φ (upd (y σ) σ)
      · rw [mask_op_of_pos ⟨hp, by rw [hwrite, hfresh]⟩,
          mask_op_of_pos (φ := fun σ => φ (upd (y σ) σ)) hp]
        simp only [measureOutcomePre, dif_pos hd]
      · rw [mask_op_of_neg (fun h => hp h.1), mask_op_of_neg (φ := fun σ => φ (upd (y σ) σ)) hp]
        simp
    · intro i _ hi
      rw [mask_op_of_neg (by
        intro h
        have he := h.2
        rw [hwrite, hfresh] at he
        exact hi he)]
      simp
    · simp
  · rw [measurePre_op_of_not_dist _ r M upd hd]
    by_cases hp : φ (upd (y σ) σ)
    · rw [mask_op_of_pos (φ := fun σ => φ (upd (y σ) σ)) hp]
      simp only [measureOutcomePre, dif_neg hd]
    · rw [mask_op_of_neg (φ := fun σ => φ (upd (y σ) σ)) hp]

end Assn

/-- A generalized single-outcome rule. The source (Axiom-Meas) is the instance
with ordinary `x`-only update and `y` fresh for `φ`, `A`, and `x`; preservation
of the ghost value alone does not express all syntactic freshness conditions. -/
theorem DerivPar.measureSource {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) (x y : σT → Fin m)
    (hwrite : ∀ i σ, x (upd i σ) = i)
    (hfresh : ∀ i σ, y (upd i σ) = y σ)
    (A : Assn σT D) (φ : σT → Prop) :
    DerivPar ((A.measureOutcomePre r M upd y).mask (fun σ => φ (upd (y σ) σ)))
      (.measure m k r M upd) (A.mask (fun σ => φ σ ∧ x σ = y σ)) := by
  rw [← Assn.measurePre_mask_eq_measureOutcomePre r M upd x y hwrite hfresh A φ]
  exact DerivPar.measure r M upd _

/-- Total-correctness version of the source per-outcome measurement rule. -/
theorem DerivTot.measureSource {m k : ℕ}
    (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → σT → σT) (x y : σT → Fin m)
    (hwrite : ∀ i σ, x (upd i σ) = i)
    (hfresh : ∀ i σ, y (upd i σ) = y σ)
    (A : Assn σT D) (φ : σT → Prop) :
    DerivTot ((A.measureOutcomePre r M upd y).mask (fun σ => φ (upd (y σ) σ)))
      (.measure m k r M upd) (A.mask (fun σ => φ σ ∧ x σ = y σ)) := by
  rw [← Assn.measurePre_mask_eq_measureOutcomePre r M upd x y hwrite hfresh A φ]
  exact DerivTot.measure r M upd _

end Qhl
