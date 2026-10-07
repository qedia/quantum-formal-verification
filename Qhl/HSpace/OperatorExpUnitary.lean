import Qhl.HSpace.OperatorExp
import Qhl.Gate.Unitary
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace Qhl
open scoped ComplexInnerProductSpace

/-- An operator with a real diagonal in an orthonormal basis is symmetric. -/
theorem isSymmetric_of_real_eigenbasis {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype ι]
    (b : Module.Basis ι ℂ E) (hb : Orthonormal ℂ b)
    (T : E →ₗ[ℂ] E) (d : ι → ℝ)
    (hd : ∀ i, T (b i) = (d i : ℂ) • b i) : T.IsSymmetric := by
  classical
  intro x y
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hd]
  simp [orthonormal_iff_ite.mp hb, mul_comm]

/-- The exponential of a real multiple of `-i H` is unitary for symmetric `H`. -/
theorem exp_negI_smul_mem_unitary {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    (H : E →ₗ[ℂ] E) (hH : H.IsSymmetric) (t : ℝ) :
    NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H.toContinuousLinearMap)
      ∈ unitary (E →L[ℂ] E) := by
  letI : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  apply IsSelfAdjoint.smul_mem_skewAdjoint
  · change star (-(Complex.I * (t : ℂ))) = -(-(Complex.I * (t : ℂ)))
    simp
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hH

/-- Hamiltonian evolution preserves the norm of every state. -/
theorem norm_exp_negI_smul_apply {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    (H : E →ₗ[ℂ] E) (hH : H.IsSymmetric) (t : ℝ) (v : E) :
    ‖NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H.toContinuousLinearMap) v‖ = ‖v‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (exp_negI_smul_mem_unitary H hH t) v

/-- The operator norm of a Hamiltonian evolution is at most one. -/
theorem norm_exp_negI_smul_le_one {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    (H : E →ₗ[ℂ] E) (hH : H.IsSymmetric) (t : ℝ) :
    ‖NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H.toContinuousLinearMap)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [norm_exp_negI_smul_apply H hH t, one_mul]

/-- Every real rescaling of a Hamiltonian generator has a contractive exponential. -/
theorem norm_exp_real_smul_negI_le_one {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    (H : E →ₗ[ℂ] E) (hH : H.IsSymmetric) (δ t : ℝ) :
    ‖NormedSpace.exp (t • ((-(Complex.I * (δ : ℂ))) • H.toContinuousLinearMap))‖ ≤ 1 := by
  have heq : t • ((-(Complex.I * (δ : ℂ))) • H.toContinuousLinearMap) =
      (-(Complex.I * ((t * δ : ℝ) : ℂ))) • H.toContinuousLinearMap := by
    rw [← smul_assoc, Complex.real_smul]
    congr 1
    push_cast
    ring
  rw [heq]
  exact norm_exp_negI_smul_le_one H hH (t * δ)

end Qhl
