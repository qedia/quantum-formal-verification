import Qhl.HSpace.LiftF
import Qhl.Gate.Unitary
import Mathlib.LinearAlgebra.Center

/-! # Complete lifting of domination by a singleton normalized Kraus operator -/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace ComplexOrder

section Collinearity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-- Rank-one positive order forces inclusion of the one-dimensional ranges. -/
theorem mem_span_of_outerLM_le {u v : E} (h : outerLM u u ≤ outerLM v v) :
    u ∈ Submodule.span ℂ {v} := by
  rw [← Submodule.orthogonal_orthogonal (Submodule.span ℂ {v})]
  apply (Submodule.mem_orthogonal _ _).mpr
  intro w hw
  have hvw : ⟪v, w⟫ = 0 :=
    (Submodule.mem_orthogonal_singleton_iff_inner_right).mp hw
  have hp := ((LinearMap.le_def _ _).mp h).re_inner_nonneg_left w
  simp only [LinearMap.sub_apply, inner_sub_left, map_sub,
    outerLM_apply, inner_smul_left, hvw, map_zero, zero_mul,
    RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re] at hp
  have hn : ‖⟪u, w⟫‖ = 0 := by nlinarith [norm_nonneg ⟪u, w⟫]
  exact inner_eq_zero_symm.mp (norm_eq_zero.mp hn)

/-- An operator preserving every pure-state ray is a scalar multiple of identity. -/
theorem eq_smul_one_of_conj_le (C : E →ₗ[ℂ] E)
    (hC : ∀ (ρ : E →ₗ[ℂ] E), ρ.IsPositive →
      C ∘ₗ ρ ∘ₗ LinearMap.adjoint C ≤ ρ) :
    ∃ a : ℂ, C = a • (1 : E →ₗ[ℂ] E) := by
  apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
  intro v hv
  have ho := hC (outerLM v v) (isPositive_outerLM_self v)
  have hc : C ∘ₗ outerLM v v ∘ₗ LinearMap.adjoint C = outerLM (C v) (C v) := by
    simpa only [LinearMap.adjoint_adjoint] using
      adjoint_comp_outerLM_comp (LinearMap.adjoint C) v v
  rw [hc] at ho
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (mem_span_of_outerLM_le ho)
  have hz := (LinearIndependent.pair_iff.mp hv) a (-1) (by simp [ha])
  norm_num at hz

/-- Domination by a unitary singleton forces proportional Kraus operators.
This is derived from all pure inputs, including their superpositions. -/
theorem eq_smul_of_conj_le_unitary (K J : E →ₗ[ℂ] E) (hJ : IsUnitary J)
    (hdom : ∀ (ρ : E →ₗ[ℂ] E), ρ.IsPositive →
      K ∘ₗ ρ ∘ₗ LinearMap.adjoint K ≤ J ∘ₗ ρ ∘ₗ LinearMap.adjoint J) :
    ∃ a : ℂ, K = a • J := by
  let C := LinearMap.adjoint J ∘ₗ K
  have hc : ∃ a : ℂ, C = a • (1 : E →ₗ[ℂ] E) := by
    apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    intro v hv
    have ho := hdom (outerLM v v) (isPositive_outerLM_self v)
    have hk : K ∘ₗ outerLM v v ∘ₗ LinearMap.adjoint K = outerLM (K v) (K v) := by
      simpa only [LinearMap.adjoint_adjoint] using
        adjoint_comp_outerLM_comp (LinearMap.adjoint K) v v
    have hj : J ∘ₗ outerLM v v ∘ₗ LinearMap.adjoint J = outerLM (J v) (J v) := by
      simpa only [LinearMap.adjoint_adjoint] using
        adjoint_comp_outerLM_comp (LinearMap.adjoint J) v v
    rw [hk, hj] at ho
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (mem_span_of_outerLM_le ho)
    have hvj : LinearMap.adjoint J (J v) = v := by
      simpa using congrArg (fun f : E →ₗ[ℂ] E => f v) hJ.1
    have hvC : a • v = C v := by
      simpa only [C, LinearMap.comp_apply, map_smul, hvj] using congrArg (LinearMap.adjoint J) ha
    have hz := (LinearIndependent.pair_iff.mp hv) a (-1) (by simp [hvC])
    norm_num at hz
  obtain ⟨a, ha⟩ := hc
  refine ⟨a, ?_⟩
  have hid : J ∘ₗ C = K := by
    dsimp [C]
    rw [← LinearMap.comp_assoc, hJ.2, Module.End.one_eq_id, LinearMap.id_comp]
  rw [← hid, ha]
  simp only [LinearMap.comp_smul, Module.End.one_eq_id, LinearMap.comp_id]

/-- Scalar conjugation exposes its real nonnegative multiplier. -/
theorem conj_smul_op (a : ℂ) (J ρ : E →ₗ[ℂ] E) :
    (a • J) ∘ₗ ρ ∘ₗ LinearMap.adjoint (a • J) =
      (a * starRingEnd ℂ a) • (J ∘ₗ ρ ∘ₗ LinearMap.adjoint J) := by
  simp only [map_smulₛₗ, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, mul_comm]

/-- The proportionality factor has a positive remaining weight. -/
theorem scalar_gap_nonneg_of_conj_le [Nontrivial E]
    (a : ℂ) (J : E →ₗ[ℂ] E) (hJ : IsUnitary J)
    (hdom : ∀ (ρ : E →ₗ[ℂ] E), ρ.IsPositive →
      (a • J) ∘ₗ ρ ∘ₗ LinearMap.adjoint (a • J) ≤
        J ∘ₗ ρ ∘ₗ LinearMap.adjoint J) :
    0 ≤ 1 - a * starRingEnd ℂ a := by
  have h := hdom 1 LinearMap.isPositive_one
  rw [conj_smul_op, Module.End.one_eq_id, LinearMap.id_comp, hJ.2] at h
  have hp := (LinearMap.le_def _ _).mp h
  rw [show (1 : E →ₗ[ℂ] E) - (a * starRingEnd ℂ a) • (1 : E →ₗ[ℂ] E) =
    (1 - a * starRingEnd ℂ a) • (1 : E →ₗ[ℂ] E) by rw [sub_smul, one_smul]] at hp
  exact (LinearMap.isPositive_one.isPositive_smul_iff one_ne_zero).mp hp

end Collinearity

section Lift

variable {L : Type*} [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {S T : Finset L}

/-- Local singleton Kraus domination remains valid on the full tensor product,
including entangled inputs. Proportionality is proved from local positive-input
domination; it is not an extra restriction on the supplied operators. -/
theorem liftF_conj_le_of_local_domination (hST : S ⊆ T)
    (K J : EndM D S) (hJ : LinearMap.adjoint J ∘ₗ J = 1)
    (hdom : ∀ ρ : EndM D S, ρ.IsPositive →
      K ∘ₗ ρ ∘ₗ LinearMap.adjoint K ≤ J ∘ₗ ρ ∘ₗ LinearMap.adjoint J)
    (R : EndM D T) (hR : R.IsPositive) :
    liftF D hST K ∘ₗ R ∘ₗ LinearMap.adjoint (liftF D hST K) ≤
      liftF D hST J ∘ₗ R ∘ₗ LinearMap.adjoint (liftF D hST J) := by
  have hu := isUnitary_of_adjoint_comp_self hJ
  obtain ⟨a, ha⟩ := eq_smul_of_conj_le_unitary K J hu hdom
  subst K
  have hgap := scalar_gap_nonneg_of_conj_le a J hu hdom
  rw [liftF_smul, conj_smul_op, LinearMap.le_def]
  have hp := (hR.conj_adjoint (liftF D hST J)).smul_of_nonneg hgap
  simpa only [sub_smul, one_smul] using hp

end Lift

end Qhl
