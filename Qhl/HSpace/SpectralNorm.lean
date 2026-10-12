import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Strict operator norm bounds and finite spectral data -/
namespace Qhl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A strict bound on the induced Hilbert-space operator norm supplies precisely
normalized real spectral data with strictly interior normalized eigenvalues. -/
theorem spectral_of_norm_lt (H : E →ₗ[ℂ] E) (hH : H.IsSymmetric)
    (lam : ℝ) (h : ‖H.toContinuousLinearMap‖ < lam) :
    0 < lam ∧ ∃ (b : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E) 
        (e : Fin (Module.finrank ℂ E) → ℝ),
      (∀ i, ‖b i‖ = 1) ∧ (∀ i, H (b i) = (e i : ℂ) • b i) ∧
      (∀ i, (e i / lam) ^ 2 < 1) := by
  have hlam : 0 < lam := lt_of_le_of_lt (norm_nonneg _) h
  refine ⟨hlam, (hH.eigenvectorBasis rfl).toBasis, hH.eigenvalues rfl, ?_, ?_, ?_⟩
  · intro i
    exact (hH.eigenvectorBasis rfl).norm_eq_one i
  · exact hH.apply_eigenvectorBasis rfl
  · intro i
    have hb := (hH.eigenvectorBasis rfl).norm_eq_one i
    have hn := H.toContinuousLinearMap.le_opNorm ((hH.eigenvectorBasis rfl) i)
    change ‖H ((hH.eigenvectorBasis rfl) i)‖ ≤ _ at hn
    rw [hH.apply_eigenvectorBasis rfl, norm_smul, RCLike.norm_ofReal, hb, mul_one,
      mul_one] at hn
    have he : |hH.eigenvalues rfl i| < lam := lt_of_le_of_lt hn h
    have hd : |hH.eigenvalues rfl i / lam| < 1 := by
      rw [abs_div, abs_of_pos hlam, div_lt_one hlam]
      exact he
    nlinarith [sq_abs (hH.eigenvalues rfl i / lam), abs_nonneg (hH.eigenvalues rfl i / lam)]

#print axioms spectral_of_norm_lt
end Qhl
