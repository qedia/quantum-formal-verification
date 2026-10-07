import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Coefficient bounds for commutators with two-site interactions -/

namespace Qhl

/-- A sum of unit-norm terms coupled to two sites has a commutator bound
that depends only on the two incident coefficients. -/
theorem norm_commutator_sum_le_of_two_sites
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → A) (Z : κ → A) (a : ι → ℝ) (b : κ → ℝ)
    (lo hi : κ → ι) (hne : ∀ j, lo j ≠ hi j)
    (hX : ∀ i, ‖X i‖ ≤ 1) (hZ : ∀ j, ‖Z j‖ ≤ 1)
    (hc : ∀ i j, i ≠ lo j → i ≠ hi j → X i * Z j = Z j * X i) :
    ‖(∑ i, (a i : ℂ) • X i) * (∑ j, (b j : ℂ) • Z j) -
      (∑ j, (b j : ℂ) • Z j) * (∑ i, (a i : ℂ) • X i)‖ ≤
      2 * ∑ j, |b j| * (|a (lo j)| + |a (hi j)|) := by
  classical
  have hterm (i : ι) (j : κ) :
      ‖((a i : ℂ) * (b j : ℂ)) • (X i * Z j - Z j * X i)‖ ≤
        2 * |b j| * ((if i = lo j then |a i| else 0) +
          (if i = hi j then |a i| else 0)) := by
    have hbase : ‖X i * Z j - Z j * X i‖ ≤ 2 := by
      calc
        _ ≤ ‖X i * Z j‖ + ‖Z j * X i‖ := norm_sub_le _ _
        _ ≤ ‖X i‖ * ‖Z j‖ + ‖Z j‖ * ‖X i‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ 1 * 1 + 1 * 1 := add_le_add
          (mul_le_mul (hX i) (hZ j) (norm_nonneg _) zero_le_one)
          (mul_le_mul (hZ j) (hX i) (norm_nonneg _) zero_le_one)
        _ = 2 := by norm_num
    by_cases hl : i = lo j
    · have hh : i ≠ hi j := hl ▸ hne j
      simp only [if_pos hl, if_neg hh, add_zero, norm_smul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      nlinarith [mul_le_mul_of_nonneg_left hbase
          (mul_nonneg (abs_nonneg (a i)) (abs_nonneg (b j)))]
    · by_cases hh : i = hi j
      · simp only [if_neg hl, if_pos hh, zero_add, norm_smul, norm_mul,
          Complex.norm_real, Real.norm_eq_abs]
        nlinarith [mul_le_mul_of_nonneg_left hbase
          (mul_nonneg (abs_nonneg (a i)) (abs_nonneg (b j)))]
      · simp [hc i j hl hh, hl, hh]
  have heq : (∑ i, (a i : ℂ) • X i) * (∑ j, (b j : ℂ) • Z j) -
      (∑ j, (b j : ℂ) • Z j) * (∑ i, (a i : ℂ) • X i) =
      ∑ j, ∑ i, ((a i : ℂ) * (b j : ℂ)) • (X i * Z j - Z j * X i) := by
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      smul_smul, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum]
    simp only [mul_comm]
    congr 1
    exact Finset.sum_comm
  rw [heq]
  calc
    _ ≤ ∑ j, ‖∑ i, ((a i : ℂ) * (b j : ℂ)) • (X i * Z j - Z j * X i)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ∑ i, 2 * |b j| * ((if i = lo j then |a i| else 0) +
        (if i = hi j then |a i| else 0)) := Finset.sum_le_sum fun j _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i j)
    _ = _ := by simp [← Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]

end Qhl
