import Qhl.HSpace.ProjectorDistance

/-! # An upper bound for the sum of two pure-state projectors -/

namespace Qhl
open scoped ComplexInnerProductSpace ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem projectorSum_cube (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    let S := outerLM u u + outerLM v v
    S * S * S + (1 - ⟪u, v⟫ * ⟪v, u⟫) • S = (2 : ℂ) • (S * S) := by
  have huu : ⟪u, u⟫ = (1 : ℂ) := by simp [inner_self_eq_norm_sq_to_K, hu]
  have hvv : ⟪v, v⟫ = (1 : ℂ) := by simp [inner_self_eq_norm_sq_to_K, hv]
  dsimp
  ext x
  simp only [Module.End.mul_apply, LinearMap.add_apply, outerLM_apply,
    inner_add_right, inner_smul_right, LinearMap.smul_apply, huu, hvv]
  module

private theorem symmetric_le_scalar [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E)
    (hT : T.IsSymmetric) (r : ℝ)
    (h : ∀ i, hT.eigenvalues rfl i ≤ r) : T ≤ (r : ℂ) • (1 : E →ₗ[ℂ] E) := by
  let b := hT.eigenvectorBasis rfl
  have hexpand : T = ∑ i, (hT.eigenvalues rfl i : ℂ) • outerLM (b i) (b i) := by
    ext x
    conv_lhs => rw [← b.sum_repr' x]
    simp only [map_sum, map_smul, b, hT.apply_eigenvectorBasis,
      LinearMap.sum_apply, LinearMap.smul_apply, outerLM_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  rw [hexpand, ← sum_outerLM_self b, Finset.smul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [le_iff_inner_le]
  intro x
  simp only [LinearMap.smul_apply, outerLM_apply, inner_smul_right]
  rw [← inner_conj_symm x (b i), Complex.mul_conj]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.le_def]
  exact ⟨mul_le_mul_of_nonneg_right (h i) (Complex.normSq_nonneg _), rfl⟩

/-- The sum of two unit-vector projectors is bounded by their overlap. -/
theorem outerLM_self_add_le [FiniteDimensional ℂ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    outerLM u u + outerLM v v ≤
      ((1 + ‖⟪u, v⟫‖ : ℝ) : ℂ) • (1 : E →ₗ[ℂ] E) := by
  let S := outerLM u u + outerLM v v
  have hS : S.IsSymmetric :=
    (InnerProductSpace.isSymmetric_rankOne_self u).add
      (InnerProductSpace.isSymmetric_rankOne_self v)
  apply symmetric_le_scalar S hS
  intro i
  let b := hS.eigenvectorBasis rfl
  let μ := hS.eigenvalues rfl i
  have hx : b i ≠ 0 := by
    intro hz
    have := b.norm_eq_one i
    rw [hz, norm_zero] at this
    exact zero_ne_one this
  have heig : S (b i) = (μ : ℂ) • b i := hS.apply_eigenvectorBasis rfl i
  have hc := congrArg (fun A : E →ₗ[ℂ] E => A (b i)) (projectorSum_cube u v hu hv)
  change (S * S * S + (1 - ⟪u, v⟫ * ⟪v, u⟫) • S) (b i) =
    ((2 : ℂ) • (S * S)) (b i) at hc
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    heig, map_smul, smul_smul, ← add_smul] at hc
  have hscalar := smul_left_injective ℂ hx hc
  rw [← inner_conj_symm v u, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hscalar
  have hreal := congrArg Complex.re hscalar
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im,
    mul_zero, zero_mul, sub_zero] at hreal
  norm_num at hreal
  change μ ≤ 1 + ‖⟪u, v⟫‖
  by_contra hn
  have hgt : 1 + ‖⟪u, v⟫‖ < μ := lt_of_not_ge hn
  have hpos : 0 < μ := by linarith [norm_nonneg ⟪u, v⟫]
  have hp : μ * ((μ - 1) ^ 2 - ‖⟪u, v⟫‖ ^ 2) = 0 := by nlinarith [hreal]
  have heq := (mul_eq_zero.mp hp).resolve_left (ne_of_gt hpos)
  nlinarith [norm_nonneg ⟪u, v⟫]

end Qhl
