import Qhl.HSpace.OperatorExp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NoncommRing

/-! # First-order product formula estimates in operator norm -/
namespace Qhl
namespace TrotterError
open NormedSpace Set
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]

omit [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A] in
private theorem norm_mul_le_of_norm_le_one_left {a b : A} (ha : ‖a‖ ≤ 1) :
    ‖a * b‖ ≤ ‖b‖ := (norm_mul_le a b).trans (by nlinarith [norm_nonneg b])

omit [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A] in
private theorem norm_mul_le_of_norm_le_one_right {a b : A} (hb : ‖b‖ ≤ 1) :
    ‖a * b‖ ≤ ‖a‖ := (norm_mul_le a b).trans (by nlinarith [norm_nonneg a])

omit [NormedAlgebra ℚ A] in
/-- Conjugation by a contractive exponential changes an operator at a rate
bounded by its commutator with the generator. -/
theorem conjugation_bound (a b : A)
    (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • a) * b * exp (t • (-a)) - b‖ ≤ ‖a * b - b * a‖ * t := by
  let f : ℝ → A := fun x => exp (x • a) * b * exp (x • (-a))
  have hd (x : ℝ) : HasDerivAt f
      (exp (x • a) * (a * b - b * a) * exp (x • (-a))) x := by
    convert ((hasDerivAt_exp_smul_const a x).mul_const b).mul
      (hasDerivAt_exp_smul_const' (-a) x) using 1
    · rfl
    · noncomm_ring
  have hbnd (x : ℝ) :
      ‖exp (x • a) * (a * b - b * a) * exp (x • (-a))‖ ≤ ‖a * b - b * a‖ := by
    have hn : ‖exp (x • (-a))‖ ≤ 1 := by simpa only [smul_neg, neg_smul] using ha (-x)
    exact (norm_mul_le_of_norm_le_one_right hn).trans
      (norm_mul_le_of_norm_le_one_left (ha x))
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x (_ : x ∈ Icc 0 t) => (hd x).hasDerivWithinAt)
    (fun x (_ : x ∈ Ico 0 t) => hbnd x) t (by constructor <;> linarith)
  simpa [f] using h

omit [NormedAlgebra ℝ A] in
private theorem exp_neg_mul_exp (a : A) : exp (-a) * exp a = 1 := by
  rw [← exp_add_of_commute (Commute.refl a).neg_left, neg_add_cancel, exp_zero]

omit [NormedAlgebra ℝ A] in
private theorem exp_mul_exp_neg (a : A) : exp a * exp (-a) = 1 := by
  rw [← exp_add_of_commute (Commute.refl a).neg_right, add_neg_cancel, exp_zero]

/-- The commutator with an exponential is bounded linearly in time. -/
theorem exp_commutator_bound (a b : A)
    (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • a) * b - b * exp (t • a)‖ ≤ ‖a * b - b * a‖ * t := by
  have he : (exp (t • a) * b * exp (t • (-a)) - b) * exp (t • a) =
      exp (t • a) * b - b * exp (t • a) := by
    rw [sub_mul, mul_assoc, smul_neg, exp_neg_mul_exp, mul_one]
  rw [← he]
  exact (norm_mul_le_of_norm_le_one_right (ha t)).trans (conjugation_bound a b ha ht)

/-- A single Lie product step has a second-order commutator error.
The hypotheses hold for skew-adjoint operators, whose exponentials are unitary. -/
theorem exp_mul_error (a b : A)
    (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hab : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) :
    ‖exp a * exp b - exp (a + b)‖ ≤ ‖a * b - b * a‖ / 2 := by
  let f : ℝ → A := fun x =>
    exp (x • (-(a + b))) * exp (x • a) * exp (x • b) - 1
  let df : ℝ → A := fun x => exp (x • (-(a + b))) *
    (exp (x • a) * b - b * exp (x • a)) * exp (x • b)
  have hd (x : ℝ) : HasDerivAt f (df x) x := by
    convert (((hasDerivAt_exp_smul_const (-(a + b)) x).mul
      (hasDerivAt_exp_smul_const' a x)).mul
      (hasDerivAt_exp_smul_const' b x)).sub_const 1 using 1
    all_goals first | rfl | (simp only [df, Pi.mul_apply]; noncomm_ring)
  have hbnd (x : ℝ) (hx : 0 ≤ x) : ‖df x‖ ≤ ‖a * b - b * a‖ * x := by
    have hn : ‖exp (x • (-(a + b)))‖ ≤ 1 := by
      simpa only [smul_neg, neg_smul] using hab (-x)
    exact (norm_mul_le_of_norm_le_one_right (hb x)).trans
      ((norm_mul_le_of_norm_le_one_left hn).trans (exp_commutator_bound a b ha hx))
  have hmajor (x : ℝ) : HasDerivAt
      (fun y : ℝ => ‖a * b - b * a‖ / 2 * y ^ 2) (‖a * b - b * a‖ * x) x := by
    convert ((hasDerivAt_id x).pow 2).const_mul (‖a * b - b * a‖ / 2) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hnorm := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := f) (a := 0) (b := 1)
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).hasDerivWithinAt)
    (by simp [f]) hmajor (fun x hx => hbnd x hx.1) (x := 1) (by norm_num)
  have he : exp (a + b) * f 1 = exp a * exp b - exp (a + b) := by
    dsimp [f]
    simp only [one_smul, mul_sub, mul_one]
    rw [← mul_assoc, ← mul_assoc, exp_mul_exp_neg, one_mul]
  rw [← he]
  exact (norm_mul_le_of_norm_le_one_left (by simpa using hab 1)).trans
    (by simpa using hnorm)

/-- The first-order product formula accumulates at most a linear number of
single-step commutator errors. -/
theorem product_formula_error (a b : A)
    (ha : ∀ t : ℝ, ‖exp (t • a)‖ ≤ 1)
    (hb : ∀ t : ℝ, ‖exp (t • b)‖ ≤ 1)
    (hab : ∀ t : ℝ, ‖exp (t • (a + b))‖ ≤ 1) (N : ℕ) :
    ‖(exp a * exp b) ^ N - exp (N • (a + b))‖ ≤
      (N : ℝ) / 2 * ‖a * b - b * a‖ := by
  have hx : ‖exp a * exp b‖ ≤ 1 :=
    (norm_mul_le_of_norm_le_one_left (by simpa using ha 1)).trans (by simpa using hb 1)
  have hy (n : ℕ) : ‖exp (a + b) ^ n‖ ≤ 1 := by
    rw [← exp_nsmul]
    simpa only [Nat.cast_smul_eq_nsmul] using hab (n : ℝ)
  have hlocal := exp_mul_error a b ha hb hab
  rw [exp_nsmul]
  induction N with
  | zero => simp
  | succ n ih =>
    have he : (exp a * exp b) ^ (n + 1) - exp (a + b) ^ (n + 1) =
        ((exp a * exp b) ^ n - exp (a + b) ^ n) * (exp a * exp b) +
        exp (a + b) ^ n * (exp a * exp b - exp (a + b)) := by
      simp only [pow_succ]
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖((exp a * exp b) ^ n - exp (a + b) ^ n) * (exp a * exp b)‖ +
          ‖exp (a + b) ^ n * (exp a * exp b - exp (a + b))‖ := norm_add_le _ _
      _ ≤ ‖(exp a * exp b) ^ n - exp (a + b) ^ n‖ +
          ‖exp a * exp b - exp (a + b)‖ := add_le_add
            (norm_mul_le_of_norm_le_one_right hx) (norm_mul_le_of_norm_le_one_left (hy n))
      _ ≤ (n : ℝ) / 2 * ‖a * b - b * a‖ + ‖a * b - b * a‖ / 2 := add_le_add ih hlocal
      _ = _ := by push_cast; ring

end TrotterError
end Qhl
