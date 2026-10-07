import Qhl.Register.Fourier

/-! # The Fourier operator on the uniform input

This follows from the defining Fourier matrix and orthogonality of its columns.
-/

namespace Qhl
open Finset
open scoped ComplexInnerProductSpace

/-- The Fourier matrix is symmetric. -/
theorem qftMat_transpose_eq (n : ℕ) : (qftMat n).transpose = qftMat n := by
  ext l m
  simp only [Matrix.transpose_apply, qftMat, fourierState_apply]
  rw [Nat.mul_comm]

/-- The independently defined Fourier operator maps the uniform state to zero. -/
theorem qftOp_allPlus (n : ℕ) :
    (qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n))) (allPlus n) = allZeros n := by
  classical
  apply PiLp.ext
  intro l
  rw [coe_qftOp, matOp_apply, allZeros_eq_deltav, deltav_apply]
  have hrow : ∑ m, qftMat n l m * allPlus n m =
      ⟪fourierState n (fun _ => false),
        fourierState n (fun i : QubitL n => l ⟨i, mem_univ i⟩)⟫ := by
    rw [fourierState_false_eq_allPlus, dot_cdv (QubitD n)]
    apply Finset.sum_congr rfl
    intro m _
    have hsym := congrArg (fun M => M l m) (qftMat_transpose_eq n)
    simp only [Matrix.transpose_apply] at hsym
    rw [← hsym]
    change fourierState n (fun i : QubitL n => l ⟨i, mem_univ i⟩) m * allPlus n m =
      star (allPlus n m) * fourierState n (fun i : QubitL n => l ⟨i, mem_univ i⟩) m
    rw [allPlus_apply]
    simp only [map_pow, map_inv₀, Complex.star_def, Complex.conj_ofReal]
    exact mul_comm _ _
  rw [hrow, inner_fourierState]
  apply if_congr
  · constructor
    · intro h
      funext i
      exact (congrFun h (i : QubitL n)).symm
    · intro h
      funext i
      exact (congrFun h ⟨i, mem_univ i⟩).symm
  · rfl
  · rfl

end Qhl
