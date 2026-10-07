import Qhl.Gate.Unitary
import Qhl.SuperOp.Basic

/-!
# G-4: measurement families

Subgoal G-4 of spec 06. A `QMeasure m E` bundles `m` measurement operators
with the completeness relation `∑ i, (Mᵢ)† ∘ Mᵢ = 1` (Decision W5: the side
condition travels *inside* the syntax, so the mass lemmas of P-4 hold
unconditionally). Outcomes are `Fin m` (Decision W8); the computational-basis
measurement of a space with basis index `α` is exposed through an equivalence
`Fin m ≃ α`.

CoqQ counterpart: the `'QM` structure of `quantum.v:3048`, here bundled per
measurement rather than as a predicate on families (`IsQMeasure` of
`SuperOp/Basic.lean:330` remains the predicate form, and `QMeasure.isQMeasure`
is the bridge).
-/

namespace Qhl

open scoped ComplexInnerProductSpace

/-- A quantum measurement with `m` outcomes on `E`: operators `Mᵢ` with
`∑ i, (Mᵢ)† ∘ Mᵢ = 1`. CoqQ `'QM` (`quantum.v:3048`). -/
structure QMeasure (m : ℕ) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] where
  /-- The measurement operator of outcome `i`. -/
  M : Fin m → (E →ₗ[ℂ] E)
  /-- The completeness relation. -/
  complete : ∑ i, LinearMap.adjoint (M i) ∘ₗ M i = 1

namespace QMeasure

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Bridge to the predicate form of a measurement family on a labelled space. -/
theorem isQMeasure {L : Type*} [DecidableEq L] {D : L → Type*}
    [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] {S : Finset L}
    (Q : QMeasure m (HS D S)) : IsQMeasure D Q.M := Q.complete

/-- The trivial one-outcome measurement (used to state `skip`-like clauses). -/
def id : QMeasure 1 E where
  M _ := 1
  complete := by
    rw [Fintype.sum_unique]
    simp [Module.End.one_eq_id]

/-- A unitary as a one-outcome measurement. -/
def ofUnitary (U : UnitaryOp E) : QMeasure 1 E where
  M _ := (U : E →ₗ[ℂ] E)
  complete := by
    rw [Fintype.sum_unique]
    exact U.2.1

end QMeasure

/-! ## The computational-basis measurement -/

section BasisMeas

variable {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}

/-- Resolution of the identity by the computational basis of
`EuclideanSpace ℂ α`. -/
theorem sum_outerLM_single :
    ∑ a : α, outerLM (EuclideanSpace.single a (1 : ℂ)) (EuclideanSpace.single a (1 : ℂ))
      = (1 : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α) := by
  have h := sum_outerLM_self (EuclideanSpace.basisFun α ℂ)
  simpa [EuclideanSpace.basisFun_apply] using h

/-- The projection onto a computational basis vector is idempotent and
self-adjoint. -/
theorem adjoint_proj_comp_proj (a : α) :
    LinearMap.adjoint
        (outerLM (EuclideanSpace.single a (1 : ℂ)) (EuclideanSpace.single a (1 : ℂ)))
      ∘ₗ outerLM (EuclideanSpace.single a (1 : ℂ)) (EuclideanSpace.single a (1 : ℂ))
      = outerLM (EuclideanSpace.single a (1 : ℂ)) (EuclideanSpace.single a (1 : ℂ)) := by
  rw [adjoint_outerLM, outerLM_comp]
  simp

/-- G-4: the computational-basis measurement of `EuclideanSpace ℂ α`, with its
outcomes renamed to `Fin m` along `e` (Decision W8). -/
noncomputable def basisMeas (e : Fin m ≃ α) : QMeasure m (EuclideanSpace ℂ α) where
  M i := outerLM (EuclideanSpace.single (e i) (1 : ℂ)) (EuclideanSpace.single (e i) (1 : ℂ))
  complete := by
    simp only [adjoint_proj_comp_proj]
    rw [Fintype.sum_equiv e _
      (fun a : α => outerLM (EuclideanSpace.single a (1 : ℂ))
        (EuclideanSpace.single a (1 : ℂ))) fun i => rfl]
    exact sum_outerLM_single

@[simp]
theorem basisMeas_M (e : Fin m ≃ α) (i : Fin m) :
    (basisMeas e).M i =
      outerLM (EuclideanSpace.single (e i) (1 : ℂ)) (EuclideanSpace.single (e i) (1 : ℂ)) :=
  rfl

/-- The computational-basis measurement with its natural outcome type, via the
canonical numbering of a finite type. -/
noncomputable def basisMeas' : QMeasure (Fintype.card α) (EuclideanSpace ℂ α) :=
  basisMeas (Fintype.equivFin α).symm

end BasisMeas

end Qhl
