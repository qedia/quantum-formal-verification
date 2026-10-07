import Qhl.HSpace.TrotterError
import Qhl.HSpace.OperatorExpUnitary

namespace Qhl

/-- First-order Hamiltonian product formula, with its finite-step commutator bound. -/
theorem hamiltonian_product_formula_error {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    (H K : E →ₗ[ℂ] E) (hH : H.IsSymmetric) (hK : K.IsSymmetric)
    (θ : ℝ) (N : ℕ) [NeZero N] :
    ‖(NormedSpace.exp ((-(Complex.I * ((θ / N : ℝ) : ℂ))) • K.toContinuousLinearMap) *
      NormedSpace.exp ((-(Complex.I * ((θ / N : ℝ) : ℂ))) • H.toContinuousLinearMap)) ^ N -
      NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • (H + K).toContinuousLinearMap)‖ ≤
      θ ^ 2 / (2 * (N : ℝ)) *
        ‖H.toContinuousLinearMap * K.toContinuousLinearMap -
          K.toContinuousLinearMap * H.toContinuousLinearMap‖ := by
  letI : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  let c : ℂ := -(Complex.I * ((θ / N : ℝ) : ℂ))
  let A := H.toContinuousLinearMap
  let B := K.toContinuousLinearMap
  have hsum : c • B + c • A = c • (H + K).toContinuousLinearMap := by
    simp [A, B, smul_add, add_comm]
  have h := TrotterError.product_formula_error (c • B) (c • A)
    (norm_exp_real_smul_negI_le_one K hK (θ / N))
    (norm_exp_real_smul_negI_le_one H hH (θ / N))
    (fun t => by
      rw [hsum]
      exact norm_exp_real_smul_negI_le_one (H + K) (hH.add hK) (θ / N) t) N
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hscale : N • (c • B + c • A) =
      (-(Complex.I * (θ : ℂ))) • (H + K).toContinuousLinearMap := by
    rw [hsum, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    dsimp [c]
    push_cast
    field_simp
  have hc : ‖c • B * (c • A) - c • A * (c • B)‖ =
      (θ / N) ^ 2 * ‖A * B - B * A‖ := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, norm_smul, norm_mul]
    have hn : ‖c‖ = |θ / N| := by simp [c, abs_div]
    rw [hn, ← sq, sq_abs, norm_sub_rev]
  rw [hscale, hc] at h
  convert h using 1
  dsimp [A, B]
  field_simp

end Qhl
