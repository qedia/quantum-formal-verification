import Qhl.SuperOp.Choi

/-!
# G-5: the initialisation channel

Subgoal G-5 of spec 06: the channel `q̄ := ∣0…0⟩` of the paper's (Init) rule,
as the Kraus map with family `|0⟩⟨x|` indexed by the classical states `x` of
the cell set. The reference state `∣0…0⟩` is `deltav D default`, pinned by the
`Inhabited` fixture of spec 06 §2 (master: `LocalBasisFamily.inhabitedB`).

Master counterpart: `ResetKrausFamily.lean:85`.
-/

namespace Qhl

open scoped ComplexInnerProductSpace

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {S : Finset L}

/-- G-5: the initialisation channel on a cell set: `ρ ↦ ∑ₓ |0⟩⟨x| ρ |x⟩⟨0|`. -/
noncomputable def initSO (S : Finset L) : SuperOp D S S :=
  kraussoOf D fun x : QIdx D S => outerLM (deltav D (default : QIdx D S)) (deltav D x)

theorem initSO_apply (x : EndM D S) :
    initSO D S x = ∑ y : QIdx D S,
      outerLM (deltav D (default : QIdx D S)) (deltav D y) ∘ₗ x ∘ₗ
        LinearMap.adjoint (outerLM (deltav D (default : QIdx D S)) (deltav D y)) := rfl

/-- The Kraus family of `initSO` satisfies the completeness relation. -/
theorem initSO_complete :
    ∑ y : QIdx D S, LinearMap.adjoint
        (outerLM (deltav D (default : QIdx D S)) (deltav D y))
      ∘ₗ outerLM (deltav D (default : QIdx D S)) (deltav D y)
      = (1 : EndM D S) := by
  have h : ∀ y : QIdx D S, LinearMap.adjoint
      (outerLM (deltav D (default : QIdx D S)) (deltav D y))
      ∘ₗ outerLM (deltav D (default : QIdx D S)) (deltav D y)
      = outerLM (deltav D y) (deltav D y) := by
    intro y
    rw [adjoint_outerLM, outerLM_comp, dv_dot]
    simp
  simp only [h]
  have hb := sum_outerLM_self (EuclideanSpace.basisFun (QIdx D S) ℂ)
  simpa [EuclideanSpace.basisFun_apply, deltav] using hb

/-- G-5: initialisation is a quantum channel (CP and trace-preserving). -/
theorem initSO_isQC : IsQC D (initSO D S) :=
  (isQC_kraussoOf_iff D _).mpr (initSO_complete D)

/-- G-5: initialisation is a quantum operation. -/
theorem initSO_isQO : IsQO D (initSO D S) := (initSO_isQC D).isQO

end Qhl
