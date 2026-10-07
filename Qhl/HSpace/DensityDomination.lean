import Qhl.Foundations.Order
import Mathlib.Analysis.Matrix.PosDef

/-! # Density-only and positive-input Kraus domination

The source calls the Accum1 comparison inputs density operators, while its cq
states use partial density operators. Both trace-one and trace-at-most-one
readings give exactly the positive-input comparison used in the semantic core.
-/

namespace Qhl

open scoped ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-- A finite positive operator with zero trace is zero. -/
theorem eq_zero_of_positive_trace_zero {ρ : E →ₗ[ℂ] E}
    (hρ : ρ.IsPositive) (ht : LinearMap.trace ℂ E ρ = 0) : ρ = 0 := by
  classical
  let b := stdOrthonormalBasis ℂ E
  have hm := (LinearMap.posSemidef_toMatrix_iff b).mpr hρ
  have hmt : (LinearMap.toMatrix b.toBasis b.toBasis ρ).trace = 0 := by
    rw [← LinearMap.trace_eq_matrix_trace ℂ b.toBasis]
    exact ht
  have hz := hm.trace_eq_zero_iff.mp hmt
  exact (LinearMap.toMatrix b.toBasis b.toBasis).injective (by simpa using hz)

/-- Normalized-density comparison implies comparison for all positive inputs,
by finite trace normalization and positive rescaling. -/
theorem conj_le_of_density1_domination (K J : E →ₗ[ℂ] E)
    (hdom : ∀ ρ : E →ₗ[ℂ] E, IsDensity1 ρ →
      K ∘ₗ ρ ∘ₗ LinearMap.adjoint K ≤ J ∘ₗ ρ ∘ₗ LinearMap.adjoint J)
    (ρ : E →ₗ[ℂ] E) (hρ : ρ.IsPositive) :
    K ∘ₗ ρ ∘ₗ LinearMap.adjoint K ≤ J ∘ₗ ρ ∘ₗ LinearMap.adjoint J := by
  by_cases hz : ρ = 0
  · simp [hz]
  let t : ℝ := (LinearMap.trace ℂ E ρ).re
  have ht0 : 0 ≤ t := (Complex.le_def.mp hρ.trace_nonneg).1
  have htrace : LinearMap.trace ℂ E ρ = (t : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.le_def.mp hρ.trace_nonneg).2.symm
  have ht : 0 < t := by
    apply lt_of_le_of_ne ht0
    intro he
    apply hz
    apply eq_zero_of_positive_trace_zero hρ
    rw [htrace, ← he]
    rfl
  have htnz : t ≠ 0 := ne_of_gt ht
  have htC : (0 : ℂ) ≤ (t : ℂ) := by exact_mod_cast ht0
  have hiC : (0 : ℂ) ≤ ((t⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast inv_nonneg.mpr ht0
  have hnormalized : IsDensity1 (((t⁻¹ : ℝ) : ℂ) • ρ) := by
    refine ⟨hρ.smul_of_nonneg hiC, ?_⟩
    rw [map_smul, htrace, smul_eq_mul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ htnz, Complex.ofReal_one]
  have hc := (LinearMap.le_def _ _).mp (hdom _ hnormalized)
  simp only [LinearMap.comp_smul, LinearMap.smul_comp] at hc
  rw [← smul_sub] at hc
  have hs := hc.smul_of_nonneg htC
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ htnz, Complex.ofReal_one,
    one_smul] at hs
  exact (LinearMap.le_def _ _).mpr hs

/-- Partial-density comparison also implies comparison for all positive inputs. -/
theorem conj_le_of_density_domination (K J : E →ₗ[ℂ] E)
    (hdom : ∀ ρ : E →ₗ[ℂ] E, IsDensity ρ →
      K ∘ₗ ρ ∘ₗ LinearMap.adjoint K ≤ J ∘ₗ ρ ∘ₗ LinearMap.adjoint J)
    (ρ : E →ₗ[ℂ] E) (hρ : ρ.IsPositive) :
    K ∘ₗ ρ ∘ₗ LinearMap.adjoint K ≤ J ∘ₗ ρ ∘ₗ LinearMap.adjoint J :=
  conj_le_of_density1_domination K J (fun R hR => hdom R hR.isDensity) ρ hρ

/-- Positive-input and normalized-density domination are equivalent. -/
theorem positive_domination_iff_density1 (K J : E →ₗ[ℂ] E) :
    (∀ ρ : E →ₗ[ℂ] E, ρ.IsPositive →
      K ∘ₗ ρ ∘ₗ LinearMap.adjoint K ≤ J ∘ₗ ρ ∘ₗ LinearMap.adjoint J) ↔
    (∀ ρ : E →ₗ[ℂ] E, IsDensity1 ρ →
      K ∘ₗ ρ ∘ₗ LinearMap.adjoint K ≤ J ∘ₗ ρ ∘ₗ LinearMap.adjoint J) :=
  ⟨fun h ρ hρ => h ρ hρ.1, fun h => conj_le_of_density1_domination K J h⟩

/-- Positive-input and partial-density domination are equivalent. -/
theorem positive_domination_iff_density (K J : E →ₗ[ℂ] E) :
    (∀ ρ : E →ₗ[ℂ] E, ρ.IsPositive →
      K ∘ₗ ρ ∘ₗ LinearMap.adjoint K ≤ J ∘ₗ ρ ∘ₗ LinearMap.adjoint J) ↔
    (∀ ρ : E →ₗ[ℂ] E, IsDensity ρ →
      K ∘ₗ ρ ∘ₗ LinearMap.adjoint K ≤ J ∘ₗ ρ ∘ₗ LinearMap.adjoint J) :=
  ⟨fun h ρ hρ => h ρ hρ.1, fun h => conj_le_of_density_domination K J h⟩

end Qhl
