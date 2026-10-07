import Qhl.Foundations.Order
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Sharp perturbation bound for pure-state projectors -/

namespace Qhl
open scoped ComplexInnerProductSpace ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private theorem projectorDifference_cube (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    let D := outerLM u u - outerLM v v
    D * D * D = (1 - ⟪u, v⟫ * ⟪v, u⟫) • D := by
  have huu : ⟪u, u⟫ = (1 : ℂ) := by simp [inner_self_eq_norm_sq_to_K, hu]
  have hvv : ⟪v, v⟫ = (1 : ℂ) := by simp [inner_self_eq_norm_sq_to_K, hv]
  dsimp
  ext x
  simp only [Module.End.mul_apply, LinearMap.sub_apply, outerLM_apply,
    inner_sub_right, inner_smul_right, LinearMap.smul_apply, huu, hvv]
  module

private theorem real_scalar_outer_mono (u : E) {a b : ℝ} (h : a ≤ b) :
    (a : ℂ) • outerLM u u ≤ (b : ℂ) • outerLM u u := by
  rw [le_iff_inner_le]
  intro x
  simp only [LinearMap.smul_apply, outerLM_apply, inner_smul_right]
  rw [← inner_conj_symm x u, Complex.mul_conj]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.le_def]
  exact ⟨mul_le_mul_of_nonneg_right h (Complex.normSq_nonneg _), rfl⟩

private theorem symmetric_le_scalar [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E)
    (hT : T.IsSymmetric) (ε : ℝ)
    (h : ∀ i, hT.eigenvalues rfl i ≤ ε) : T ≤ (ε : ℂ) • (1 : E →ₗ[ℂ] E) := by
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
  exact Finset.sum_le_sum fun i _ => real_scalar_outer_mono (b i) (h i)

/-- Unit-vector projectors are Lipschitz with sharp constant one in Löwner order. -/
theorem outerLM_self_le_add_of_norm_sub_le [FiniteDimensional ℂ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {ε : ℝ}
    (hε : 0 ≤ ε) (hdist : ‖u - v‖ ≤ ε) :
    outerLM u u ≤ outerLM v v + (ε : ℂ) • (1 : E →ₗ[ℂ] E) := by
  let D := outerLM u u - outerLM v v
  have hD : D.IsSymmetric :=
    (InnerProductSpace.isSymmetric_rankOne_self u).sub
      (InnerProductSpace.isSymmetric_rankOne_self v)
  have hbound : D ≤ (ε : ℂ) • (1 : E →ₗ[ℂ] E) := by
    apply symmetric_le_scalar D hD ε
    intro i
    let b := hD.eigenvectorBasis rfl
    let μ := hD.eigenvalues rfl i
    have hx : b i ≠ 0 := by
      intro hz
      have := b.norm_eq_one i
      rw [hz, norm_zero] at this
      exact zero_ne_one this
    have heig : D (b i) = (μ : ℂ) • b i := hD.apply_eigenvectorBasis rfl i
    have hc := congrArg (fun A : E →ₗ[ℂ] E => A (b i)) (projectorDifference_cube u v hu hv)
    change (D * D * D) (b i) = (1 - ⟪u, v⟫ * ⟪v, u⟫) • D (b i) at hc
    simp only [Module.End.mul_apply, heig, map_smul] at hc
    rw [← inner_conj_symm v u, Complex.mul_conj] at hc
    have hscalar := smul_left_injective ℂ hx (by simpa only [smul_smul] using hc)
    have hreal := congrArg Complex.re hscalar
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      mul_zero, zero_mul, sub_zero] at hreal
    have hsq : 1 - Complex.normSq ⟪u, v⟫ ≤ ε ^ 2 := by
      have hn := norm_sub_sq (𝕜 := ℂ) u v
      rw [hu, hv] at hn
      change ‖u - v‖ ^ 2 = 1 ^ 2 - 2 * ⟪u, v⟫.re + 1 ^ 2 at hn
      have he := sq_le_sq₀ (norm_nonneg (u-v)) hε |>.mpr hdist
      rw [Complex.normSq_apply]
      nlinarith [sq_nonneg (⟪u, v⟫.re - 1), sq_nonneg ⟪u, v⟫.im]
    change μ ≤ ε
    by_contra hn
    have hpos : 0 < μ := lt_of_le_of_lt hε (lt_of_not_ge hn)
    have heq : μ ^ 2 = 1 - Complex.normSq ⟪u, v⟫ := by nlinarith
    nlinarith
  have := (sub_le_iff_le_add).mp hbound
  simpa only [D, add_comm] using this

end Qhl
