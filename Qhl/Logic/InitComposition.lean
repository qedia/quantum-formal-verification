import Qhl.Logic.Assertion

/-! # Composition of disjoint block initializations

The finite-block channel is the composition of the channels on disjoint parts.
This is an identity of the existing channels, without changing their semantics.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]

/-- The empty block initialization is the identity channel. -/
theorem initLift_empty : initLift (D := D) ∅ = LinearMap.id := by
  have hk : outerLM (deltav D (default : QIdx D ∅))
      (deltav D (default : QIdx D ∅)) = (1 : EndM D ∅) := by
    have h := sum_outerLM_self (EuclideanSpace.basisFun (QIdx D ∅) ℂ)
    simp only [EuclideanSpace.basisFun_apply, ← deltav_def] at h
    rw [Fintype.sum_eq_single (default : QIdx D ∅) (fun y hy =>
      (hy (Subsingleton.elim _ _)).elim)] at h
    exact h
  have hi : initSO D ∅ = LinearMap.id := by
    apply LinearMap.ext
    intro A
    rw [initSO_apply, Fintype.sum_eq_single (default : QIdx D ∅) (fun y hy =>
      (hy (Subsingleton.elim _ _)).elim), hk]
    simp [Module.End.one_eq_id]
  rw [initLift, hi, liftSO_id]

/-- Resetting disjoint blocks composes to resetting their union. -/
theorem initLift_union (S T : Finset L) (hd : Disjoint S T) :
    initLift (D := D) (S ∪ T) = initLift S ∘ₗ initLift T := by
  rw [initLift_eq_kraussoOf, initLift_eq_kraussoOf, initLift_eq_kraussoOf,
    kraussoOf_comp]
  have hm : QIdx.merge D (default : QIdx D S) (default : QIdx D T) =
      (default : QIdx D (S ∪ T)) := by
    funext i
    simp only [QIdx.merge]
    split_ifs <;> rfl
  have hk (p : QIdx D S × QIdx D T) :
      liftF D (subset_univ S) (outerLM (deltav D default) (deltav D p.1)) ∘ₗ
        liftF D (subset_univ T) (outerLM (deltav D default) (deltav D p.2)) =
      liftF D (subset_univ (S ∪ T))
        (outerLM (deltav D default) (deltav D ((splitEquiv D hd).symm p))) := by
    rw [← liftF_sdot D (subset_univ (S ∪ T)), sdotf_ten D hd,
      tenf_outerLM, deltav_merge D hd, deltav_merge D hd, hm]
    rfl
  simp only [hk]
  apply LinearMap.ext
  intro A
  simp only [kraussoOf_apply]
  exact ((splitEquiv D hd).symm.sum_comp fun x =>
    liftF D (subset_univ (S ∪ T)) (outerLM (deltav D default) (deltav D x)) ∘ₗ A ∘ₗ
      LinearMap.adjoint
        (liftF D (subset_univ (S ∪ T)) (outerLM (deltav D default) (deltav D x)))).symm

/-- An empty initialization does not change a weakest precondition. -/
theorem Assn.initPre_empty {σT : Type*} (A : Assn σT D) :
    A.initPre (fun _ => ∅) = A := by
  apply Assn.ext
  funext σ
  rw [Assn.initPre_op, initLift_empty]
  apply endM_ext_of_trace_comp D
  intro x
  rw [trace_comp_dualSO, LinearMap.id_apply]

/-- Backward transformers compose in reverse channel order on disjoint blocks. -/
theorem Assn.initPre_union {σT : Type*} (A : Assn σT D)
    (S T : σT → Finset L) (hd : ∀ σ, Disjoint (S σ) (T σ)) :
    (A.initPre T).initPre S = A.initPre (fun σ => S σ ∪ T σ) := by
  apply Assn.ext
  funext σ
  simp only [Assn.initPre_op]
  apply endM_ext_of_trace_comp D
  intro x
  rw [trace_comp_dualSO, trace_comp_dualSO, trace_comp_dualSO,
    Finset.union_comm (S σ), initLift_union (T σ) (S σ) (hd σ).symm,
    LinearMap.comp_apply]

end Qhl
