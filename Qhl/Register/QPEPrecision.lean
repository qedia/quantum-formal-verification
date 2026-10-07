import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Int.Interval

/-!
# The numeric precision core of Nielsen & Chuang §5.2.1 QPE — (5.25)–(5.35)

**PRECISION-ANALYSIS CORE.**  This module is a *standalone precision analysis*: pure
mathematics with **no program semantics** whatsoever.  It is **NOT** composed into the
exact-phase QPE triple (`Qhl/Examples/QPETriple.lean`, `qpeDeriv`/`qpeValid`), and nothing
on the exact-phase path imports it — that dependency does not exist in either direction.
Its numeric bounds reach the quantum side through `Qhl/Register/QPEPrecisionBridge.lean`,
where they are turned into basis-outcome amplitude bounds and consumed by the operational
approximate-QPE example `Qhl/Examples/QPEApproxTriple.lean`.

This file is a **self-contained pure-analysis** development.  It imports nothing from `Qhl`:
only Mathlib.  It formalises the numeric chain N&C (5.25)–(5.35), stated abstractly in a real
phase offset `Δ` (and, for the tail bound, in a sub-resolution offset `δ`), with no reference
to quantum registers, programs, assertions or Hoare triples.

The object of study is the normalised geometric amplitude
`qpeAmp N Δ = (1/N) ∑_{k<N} exp(2πi k Δ)`.  In textbook QPE its squared modulus is
*informally* the readout probability of an outcome sitting a fractional distance `Δ` from the
true eigenphase; **in this package that reading is not a theorem at all** — there is no
statement here relating `qpeAmp` to any program's measurement distribution.

STATUS / classification (honest scope):
* Everything in this file is unconditional pure mathematics: the tail bound `qpeTailBound`,
  the Parseval normalisation `qpeAmp_parseval`, and the headline
  `qpeSuccessBound_unconditional` have no undischarged hypotheses.
* **NOT formalised here:** that these amplitudes are the Born weights of the QPE program's
  measurement outcomes at inexact eigenphases.  Nothing in *this* file mentions a register,
  a state or a program.  That passage is made elsewhere: `Qhl/Register/QPEPrecisionBridge.lean`
  identifies `qpeAmp` with the Fourier overlaps of the kicked stage-2 state and re-indexes the
  good estimates by computational-basis bit vectors (`qpe_readout_successBound`), and
  `Qhl/Examples/QPEApproxTriple.lean` turns that into a `validTot` weakest-precondition triple
  for the phase-estimation program with the good-outcome effect as postcondition.
* Honest scope of that operational endpoint: it is stated **at the intended input state,
  through the wp precondition**, not as a universal scaled-projector triple — validity over
  *all* density operators would force the operator inequality `c·∣0,ψ⟩⟨0,ψ∣ ≤ wp(P_good)`,
  which is false whenever the success probability `c` is `< 1` (states in the bad-outcome
  subspace refute it).  The exact-phase triple `qpeDeriv`/`qpeValid` remains the
  *exact-case* program-correctness endpoint; this file is the numeric analysis behind the
  approximate one.
-/

namespace Qhl

open scoped BigOperators

/-- **N&C (5.25).**  The normalised geometric amplitude of Quantum Phase Estimation:
`qpeAmp N Δ = (1/N) ∑_{k<N} exp(2πi·kΔ)`.  `Δ` is the (real) fractional offset between the
measured register value and the true scaled eigenphase.  Only the phases matter, so this is
stated with no program semantics. -/
noncomputable def qpeAmp (N : ℕ) (Δ : ℝ) : ℂ :=
    (1 / (N : ℂ)) * ∑ k ∈ Finset.range N,
      Complex.exp ((2 * Real.pi * ((k : ℝ) * Δ) : ℝ) * Complex.I)

/-- The base phase `exp(2πiΔ)` equals `1` iff `Δ` is an integer.  Under the mild bound
`|Δ| < 1` and `Δ ≠ 0` (the regime of interest) the phase is therefore genuinely `≠ 1`,
which is exactly the hypothesis needed to sum the geometric series (N&C 5.26). -/
theorem exp_phase_ne_one (Δ : ℝ) (hΔ0 : Δ ≠ 0) (hΔ : |Δ| < 1) :
    Complex.exp ((2 * Real.pi * Δ : ℝ) * Complex.I) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have h2piI : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    simp [this, Complex.I_ne_zero]
  have key : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (Δ : ℂ)
      = (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (n : ℂ) := by
    push_cast at hn
    linear_combination hn
  have hΔn : (Δ : ℝ) = (n : ℝ) := by
    have hc : (Δ : ℂ) = ((n : ℝ) : ℂ) := by
      have := mul_left_cancel₀ h2piI key
      push_cast at this ⊢
      linear_combination this
    exact_mod_cast hc
  rw [hΔn] at hΔ
  have hn1 : |n| < 1 := by exact_mod_cast hΔ
  have hn0 : n = 0 := by
    have := abs_lt.1 hn1
    omega
  rw [hn0] at hΔn
  simp only [Int.cast_zero] at hΔn
  exact hΔ0 hΔn

/-- **N&C (5.26).**  Closed form of the geometric amplitude when the base phase is `≠ 1`:
`qpeAmp N Δ = (1/N) · (exp(2πi·NΔ) − 1)/(exp(2πiΔ) − 1)`.  Proved from `geom_sum_eq` after
rewriting `exp(2πi·kΔ) = exp(2πiΔ)^k`. -/
theorem qpeAmp_closed (N : ℕ) (Δ : ℝ)
    (h : Complex.exp ((2 * Real.pi * Δ : ℝ) * Complex.I) ≠ 1) :
    qpeAmp N Δ = (1 / (N : ℂ)) *
      ((Complex.exp ((2 * Real.pi * ((N : ℝ) * Δ) : ℝ) * Complex.I) - 1) /
       (Complex.exp ((2 * Real.pi * Δ : ℝ) * Complex.I) - 1)) := by
  unfold qpeAmp
  have hs : (∑ k ∈ Finset.range N,
      Complex.exp ((2 * Real.pi * ((k : ℝ) * Δ) : ℝ) * Complex.I))
      = ∑ k ∈ Finset.range N, Complex.exp ((2 * Real.pi * Δ : ℝ) * Complex.I) ^ k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hs, geom_sum_eq h N]
  have hzN : Complex.exp ((2 * Real.pi * Δ : ℝ) * Complex.I) ^ N
      = Complex.exp ((2 * Real.pi * ((N : ℝ) * Δ) : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hzN]

/-- **N&C (5.31), numerator bound.**  `‖exp(2πi·NΔ) − 1‖ ≤ 2`, from the sine form
`‖exp(ix) − 1‖ = ‖2 sin(x/2)‖` and `|sin| ≤ 1`. -/
theorem norm_numerator_le (N : ℕ) (Δ : ℝ) :
    ‖Complex.exp ((2 * Real.pi * ((N : ℝ) * Δ) : ℝ) * Complex.I) - 1‖ ≤ 2 := by
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  have hs : |Real.sin ((2 * Real.pi * ((N : ℝ) * Δ)) / 2)| ≤ 1 :=
    abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  nlinarith [hs, abs_nonneg (Real.sin ((2 * Real.pi * ((N : ℝ) * Δ)) / 2))]

/-- **N&C (5.32), denominator bound (Jordan's inequality).**  For `|Δ| ≤ 1/2`,
`4|Δ| ≤ ‖exp(2πiΔ) − 1‖ = 2|sin(πΔ)|`, using `2/π·|x| ≤ |sin x|` for `|x| ≤ π/2`. -/
theorem norm_denominator_ge (Δ : ℝ) (hΔ : |Δ| ≤ 1 / 2) :
    4 * |Δ| ≤ ‖Complex.exp ((2 * Real.pi * Δ : ℝ) * Complex.I) - 1‖ := by
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
  have harg : (2 * Real.pi * Δ) / 2 = Real.pi * Δ := by ring
  rw [harg]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  have hpi := Real.pi_pos
  have hx : |Real.pi * Δ| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith [abs_nonneg Δ]
  have hj := Real.mul_abs_le_abs_sin hx
  have he : 2 / Real.pi * |Real.pi * Δ| = 2 * |Δ| := by
    rw [abs_mul, abs_of_pos hpi]
    field_simp
  rw [he] at hj
  linarith

/-- **N&C (5.33), per-outcome amplitude bound.**  For `Δ ≠ 0`, `|Δ| ≤ 1/2` and `N > 0`,
`‖qpeAmp N Δ‖ ≤ 1/(2N|Δ|)`. -/
theorem qpeAmp_norm_le (N : ℕ) (hN : 0 < N) (Δ : ℝ) (hΔ0 : Δ ≠ 0) (hΔ : |Δ| ≤ 1 / 2) :
    ‖qpeAmp N Δ‖ ≤ 1 / (2 * (N : ℝ) * |Δ|) := by
  have hΔ1 : |Δ| < 1 := lt_of_le_of_lt hΔ (by norm_num)
  have hne := exp_phase_ne_one Δ hΔ0 hΔ1
  rw [qpeAmp_closed N Δ hne]
  simp only [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have hnum := norm_numerator_le N Δ
  have habs : 0 < |Δ| := abs_pos.2 hΔ0
  have hden := norm_denominator_ge Δ hΔ
  have hden0 : 0 < ‖Complex.exp ((2 * Real.pi * Δ : ℝ) * Complex.I) - 1‖ :=
    lt_of_lt_of_le (by positivity) hden
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  calc 1 / (N : ℝ) *
        (‖Complex.exp ((2 * Real.pi * ((N : ℝ) * Δ) : ℝ) * Complex.I) - 1‖ /
         ‖Complex.exp ((2 * Real.pi * Δ : ℝ) * Complex.I) - 1‖)
      ≤ 1 / (N : ℝ) * (2 / (4 * |Δ|)) := by
        gcongr
    _ = 1 / (2 * (N : ℝ) * |Δ|) := by
        field_simp
        ring

/-- **N&C (5.33), squared form.**  For `Δ ≠ 0`, `|Δ| ≤ 1/2` and `N > 0`,
`‖qpeAmp N Δ‖² ≤ 1/(4 N² Δ²)`.  This is the per-outcome probability bound. -/
theorem qpeAmp_sq_le (N : ℕ) (hN : 0 < N) (Δ : ℝ) (hΔ0 : Δ ≠ 0) (hΔ : |Δ| ≤ 1 / 2) :
    ‖qpeAmp N Δ‖ ^ 2 ≤ 1 / (4 * (N : ℝ) ^ 2 * Δ ^ 2) := by
  have h := qpeAmp_norm_le N hN Δ hΔ0 hΔ
  have hpow : ‖qpeAmp N Δ‖ ^ 2 ≤ (1 / (2 * (N : ℝ) * |Δ|)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  have heq : (1 / (2 * (N : ℝ) * |Δ|)) ^ 2 = 1 / (4 * (N : ℝ) ^ 2 * Δ ^ 2) := by
    rw [div_pow, one_pow]
    congr 1
    rw [mul_pow, mul_pow, sq_abs]
    ring
  rw [heq] at hpow
  exact hpow

/-- **Positive-side tail (N&C 5.34).**  Over the outcomes lying a positive distance
`m ∈ (e, N/2]` above the true value, the leakage probability is bounded by `1/(4(e−1))`.
The per-term bound `qpeAmp_sq_le` with `Δ = (m−δ)/N` gives `‖amp‖² ≤ 1/(4(m−δ)²) ≤ 1/(4(m−1)²)`
(using `0 ≤ δ < 1`); re-indexing `i = m−1` and applying `sum_Ioc_inv_sq_le_sub` (with
`k = e−1`) telescopes the inverse squares. -/
theorem tailPos_sum_le (N : ℕ) (hEven : Even N) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (e : ℕ) (he : 2 ≤ e) (heN : 2 * e < N) :
    ∑ m ∈ Finset.Ioc e (N / 2), ‖qpeAmp N (((m : ℝ) - δ) / N)‖ ^ 2
      ≤ 1 / (4 * ((e : ℝ) - 1)) := by
  have hNN : 2 * (N / 2) = N := Nat.two_mul_div_two_of_even hEven
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNhalf : ((N / 2 : ℕ) : ℝ) = (N : ℝ) / 2 := by
    have : (2 : ℝ) * ((N / 2 : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast hNN
    linarith
  have step : ∀ m ∈ Finset.Ioc e (N / 2),
      ‖qpeAmp N (((m : ℝ) - δ) / N)‖ ^ 2 ≤ 1 / 4 * (((m - 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    obtain ⟨hm1, hm2⟩ := hm
    have hmge : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 ≤ m)
    have hmδpos : 0 < (m : ℝ) - δ := by linarith
    have hΔ0 : ((m : ℝ) - δ) / N ≠ 0 := div_ne_zero (ne_of_gt hmδpos) (ne_of_gt hNr)
    have hmN : (m : ℝ) ≤ (N : ℝ) / 2 := by
      have : (m : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast hm2
      rw [hNhalf] at this; exact this
    have hΔle : |((m : ℝ) - δ) / N| ≤ 1 / 2 := by
      rw [abs_of_pos (by positivity), div_le_iff₀ hNr]
      linarith
    have hsq := qpeAmp_sq_le N hNpos (((m : ℝ) - δ) / N) hΔ0 hΔle
    have hden : 4 * (N : ℝ) ^ 2 * (((m : ℝ) - δ) / N) ^ 2 = 4 * ((m : ℝ) - δ) ^ 2 := by
      field_simp
    rw [hden] at hsq
    have hcast : (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 := by
      have h1 : 1 ≤ m := by omega
      rw [Nat.cast_sub h1, Nat.cast_one]
    rw [hcast]
    have hpos0 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    have hpos1 : 0 < ((m : ℝ) - 1) ^ 2 := by positivity
    have hle : ((m : ℝ) - 1) ^ 2 ≤ ((m : ℝ) - δ) ^ 2 := by nlinarith
    have hfin : 1 / (4 * ((m : ℝ) - δ) ^ 2) ≤ 1 / 4 * (((m : ℝ) - 1) ^ 2)⁻¹ := by
      rw [one_div, mul_inv, one_div]
      gcongr
    exact le_trans hsq hfin
  calc ∑ m ∈ Finset.Ioc e (N / 2), ‖qpeAmp N (((m : ℝ) - δ) / N)‖ ^ 2
      ≤ ∑ m ∈ Finset.Ioc e (N / 2), 1 / 4 * (((m - 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum step
    _ = 1 / 4 * ∑ m ∈ Finset.Ioc e (N / 2), (((m - 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ = 1 / 4 * ∑ i ∈ Finset.Ioc (e - 1) (N / 2 - 1), (((i : ℝ)) ^ 2)⁻¹ := by
        congr 1
        apply Finset.sum_nbij' (fun m => m - 1) (fun i => i + 1)
        · intro m hm; rw [Finset.mem_Ioc] at hm ⊢; omega
        · intro i hi; rw [Finset.mem_Ioc] at hi ⊢; omega
        · intro m hm; rw [Finset.mem_Ioc] at hm; omega
        · intro i hi; rw [Finset.mem_Ioc] at hi; omega
        · intro _ _; rfl
    _ ≤ 1 / 4 * (((e - 1 : ℕ) : ℝ)⁻¹ - ((N / 2 - 1 : ℕ) : ℝ)⁻¹) := by
        gcongr
        exact sum_Ioc_inv_sq_le_sub (by omega) (by omega)
    _ ≤ 1 / 4 * (((e - 1 : ℕ) : ℝ)⁻¹) := by
        have : (0 : ℝ) ≤ ((N / 2 - 1 : ℕ) : ℝ)⁻¹ := by positivity
        nlinarith
    _ = 1 / (4 * ((e : ℝ) - 1)) := by
        have h1 : ((e - 1 : ℕ) : ℝ) = (e : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        rw [h1]
        have he1 : (0 : ℝ) < (e : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
          linarith
        field_simp

/-- **Negative-side tail (N&C 5.34).**  Over the outcomes lying a distance `m ∈ (e, N/2−1]`
below the true value (signed offset `Δ = (−m−δ)/N`), the leakage is bounded by `1/(4e)`.
Here `‖amp‖² ≤ 1/(4(m+δ)²) ≤ 1/(4m²)` (using `0 ≤ δ`), and `sum_Ioc_inv_sq_le_sub` with
`k = e` closes it directly (no index shift, unlike the positive side). -/
theorem tailNeg_sum_le (N : ℕ) (hEven : Even N) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (e : ℕ) (he : 2 ≤ e) (heN : 2 * e < N) :
    ∑ m ∈ Finset.Ioc e (N / 2 - 1), ‖qpeAmp N ((-(m : ℝ) - δ) / N)‖ ^ 2
      ≤ 1 / (4 * (e : ℝ)) := by
  have hNN : 2 * (N / 2) = N := Nat.two_mul_div_two_of_even hEven
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNhalf : ((N / 2 : ℕ) : ℝ) = (N : ℝ) / 2 := by
    have : (2 : ℝ) * ((N / 2 : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast hNN
    linarith
  have step : ∀ m ∈ Finset.Ioc e (N / 2 - 1),
      ‖qpeAmp N ((-(m : ℝ) - δ) / N)‖ ^ 2 ≤ 1 / 4 * (((m : ℝ)) ^ 2)⁻¹ := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    obtain ⟨hm1, hm2⟩ := hm
    have hmge : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 ≤ m)
    have hΔ0 : (-(m : ℝ) - δ) / N ≠ 0 := by
      apply div_ne_zero _ (ne_of_gt hNr)
      have : (-(m : ℝ) - δ) < 0 := by linarith
      exact ne_of_lt this
    have hmupper : (m : ℝ) + δ ≤ (N : ℝ) / 2 := by
      have hm2' : (m : ℝ) ≤ ((N / 2 - 1 : ℕ) : ℝ) := by exact_mod_cast hm2
      have hcast2 : ((N / 2 - 1 : ℕ) : ℝ) = (N : ℝ) / 2 - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one, hNhalf]
      rw [hcast2] at hm2'
      linarith
    have hΔle : |(-(m : ℝ) - δ) / N| ≤ 1 / 2 := by
      rw [abs_div, abs_of_neg (by linarith : (-(m : ℝ) - δ) < 0),
          abs_of_pos hNr, div_le_iff₀ hNr]
      linarith
    have hsq := qpeAmp_sq_le N hNpos ((-(m : ℝ) - δ) / N) hΔ0 hΔle
    have hden : 4 * (N : ℝ) ^ 2 * ((-(m : ℝ) - δ) / N) ^ 2 = 4 * ((m : ℝ) + δ) ^ 2 := by
      field_simp; ring
    rw [hden] at hsq
    have hpos0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hle : ((m : ℝ)) ^ 2 ≤ ((m : ℝ) + δ) ^ 2 := by nlinarith
    have hfin : 1 / (4 * ((m : ℝ) + δ) ^ 2) ≤ 1 / 4 * (((m : ℝ)) ^ 2)⁻¹ := by
      rw [one_div, mul_inv, one_div]
      gcongr
    exact le_trans hsq hfin
  calc ∑ m ∈ Finset.Ioc e (N / 2 - 1), ‖qpeAmp N ((-(m : ℝ) - δ) / N)‖ ^ 2
      ≤ ∑ m ∈ Finset.Ioc e (N / 2 - 1), 1 / 4 * (((m : ℝ)) ^ 2)⁻¹ :=
        Finset.sum_le_sum step
    _ = 1 / 4 * ∑ m ∈ Finset.Ioc e (N / 2 - 1), (((m : ℝ)) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ 1 / 4 * (((e : ℕ) : ℝ)⁻¹ - ((N / 2 - 1 : ℕ) : ℝ)⁻¹) := by
        gcongr
        exact sum_Ioc_inv_sq_le_sub (by omega) (by omega)
    _ ≤ 1 / 4 * (((e : ℕ) : ℝ)⁻¹) := by
        have : (0 : ℝ) ≤ ((N / 2 - 1 : ℕ) : ℝ)⁻¹ := by positivity
        nlinarith
    _ = 1 / (4 * (e : ℝ)) := by
        have he0 : (0 : ℝ) < (e : ℝ) := by
          have : (2 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
          linarith
        field_simp

/-- **N&C (5.34), the two-sided tail bound — numeric core of the precision theorem.**

The QPE outcomes are labelled by one full period of `N` consecutive integers
`j ∈ [1 − N/2, N/2]`; `j` is the signed, wrapped distance of the measured value from the
true integer `b`, and the per-outcome offset is `Δ_j = (j − δ)/N`, where `δ = 2^t φ − b ∈
[0,1)` is the sub-resolution part of the phase.  We use the window `[1 − N/2, N/2]` rather
than the symmetric-looking `[−N/2, N/2 − 1]`: because `δ ≥ 0`, this is the honest choice
that keeps EVERY offset in `|Δ_j| ≤ 1/2` (Jordan's regime), with no boundary term needing a
periodicity shift.  It has exactly `N` elements, one per outcome.

The "bad" set is everything more than `e` away from `b`.  Splitting into the positive side
`[e+1, N/2]` and negative side `[1−N/2, −(e+1)]` and applying the one-sided bounds gives
`1/(4(e−1)) + 1/(4e) ≤ 1/(2(e−1))`.  The constant `1/(2(e−1))` is exactly N&C's. -/
theorem qpeTailBound (N : ℕ) (hEven : Even N) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (e : ℕ) (he : 2 ≤ e) (heN : 2 * e < N) :
    ∑ j ∈ (Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) ((N / 2 : ℕ) : ℤ) \
             Finset.Icc (-(e : ℤ)) (e : ℤ)),
      ‖qpeAmp N (((j : ℝ) - δ) / N)‖ ^ 2 ≤ 1 / (2 * ((e : ℝ) - 1)) := by
  have hNN := Nat.two_mul_div_two_of_even hEven
  -- Decompose the bad set into negative side `B` and positive side `A`.
  have hsplit : Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) ((N / 2 : ℕ) : ℤ) \
        Finset.Icc (-(e : ℤ)) (e : ℤ)
      = Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) (-(e : ℤ) - 1) ∪
        Finset.Icc ((e : ℤ) + 1) ((N / 2 : ℕ) : ℤ) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) (-(e : ℤ) - 1))
      (Finset.Icc ((e : ℤ) + 1) ((N / 2 : ℕ) : ℤ)) := by
    rw [Finset.disjoint_left]
    intro x hxB hxA
    rw [Finset.mem_Icc] at hxB hxA
    omega
  -- Re-index the positive side `A` to a natural-number `Ioc`.
  have hA : ∑ j ∈ Finset.Icc ((e : ℤ) + 1) ((N / 2 : ℕ) : ℤ),
        ‖qpeAmp N (((j : ℝ) - δ) / N)‖ ^ 2
      = ∑ m ∈ Finset.Ioc e (N / 2), ‖qpeAmp N (((m : ℝ) - δ) / N)‖ ^ 2 := by
    apply Finset.sum_bij' (fun (j : ℤ) _ => j.toNat) (fun (m : ℕ) _ => (m : ℤ))
    · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_Ioc]; omega
    · intro m hm; rw [Finset.mem_Ioc] at hm; rw [Finset.mem_Icc]; omega
    · intro j hj; rw [Finset.mem_Icc] at hj; omega
    · intro m hm; rw [Finset.mem_Ioc] at hm; omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      have hj0 : (0 : ℤ) ≤ j := by omega
      have hcast : ((j.toNat : ℝ)) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hj0
      rw [hcast]
  -- Re-index the negative side `B` to a natural-number `Ioc` via `m = -j`.
  have hB : ∑ j ∈ Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) (-(e : ℤ) - 1),
        ‖qpeAmp N (((j : ℝ) - δ) / N)‖ ^ 2
      = ∑ m ∈ Finset.Ioc e (N / 2 - 1), ‖qpeAmp N ((-(m : ℝ) - δ) / N)‖ ^ 2 := by
    apply Finset.sum_bij' (fun (j : ℤ) _ => (-j).toNat) (fun (m : ℕ) _ => -(m : ℤ))
    · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_Ioc]; omega
    · intro m hm; rw [Finset.mem_Ioc] at hm; rw [Finset.mem_Icc]; omega
    · intro j hj; rw [Finset.mem_Icc] at hj; omega
    · intro m hm; rw [Finset.mem_Ioc] at hm; omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      have hj0 : (0 : ℤ) ≤ -j := by omega
      have hcast : (((-j).toNat : ℝ)) = -(j : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hj0
      rw [hcast, neg_neg]
  rw [hsplit, Finset.sum_union hdisj, hB, hA]
  have hp := tailPos_sum_le N hEven δ hδ0 hδ1 e he heN
  have hn := tailNeg_sum_le N hEven δ hδ0 hδ1 e he heN
  have he1 : (0 : ℝ) < (e : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    linarith
  have he0 : (0 : ℝ) < (e : ℝ) := by linarith
  have hcomb : 1 / (4 * (e : ℝ)) ≤ 1 / (4 * ((e : ℝ) - 1)) := by
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  have heq2 : 1 / (2 * ((e : ℝ) - 1)) = 1 / (4 * ((e : ℝ) - 1)) + 1 / (4 * ((e : ℝ) - 1)) := by
    field_simp
    ring
  linarith [hp, hn, hcomb, heq2]

/-- **N&C (5.35), the headline precision bound (arithmetic complement of the tail).**

Given completeness of the readout distribution over one full period — the hypothesis
`hsum` that the `‖qpeAmp‖²` sum to `1` — the probability of measuring within `e` of the
true value is at least `1 − 1/(2(e−1))`.  This is a pure corollary of `qpeTailBound` and
`Finset.sum_sdiff`; `hsum` (Parseval / total probability `= 1`) is discharged
unconditionally by `qpeAmp_parseval` below (see `qpeSuccessBound_unconditional`). -/
theorem qpeSuccessBound (N : ℕ) (hEven : Even N) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (e : ℕ) (he : 2 ≤ e) (heN : 2 * e < N)
    (hsum : ∑ j ∈ Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) ((N / 2 : ℕ) : ℤ),
      ‖qpeAmp N (((j : ℝ) - δ) / N)‖ ^ 2 = 1) :
    (1 : ℝ) - 1 / (2 * ((e : ℝ) - 1)) ≤
      ∑ j ∈ Finset.Icc (-(e : ℤ)) (e : ℤ), ‖qpeAmp N (((j : ℝ) - δ) / N)‖ ^ 2 := by
  have hNN := Nat.two_mul_div_two_of_even hEven
  have hsub : Finset.Icc (-(e : ℤ)) (e : ℤ) ⊆
      Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) ((N / 2 : ℕ) : ℤ) := by
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    omega
  have hsd := Finset.sum_sdiff (f := fun j : ℤ => ‖qpeAmp N (((j : ℝ) - δ) / N)‖ ^ 2) hsub
  have htail := qpeTailBound N hEven δ hδ0 hδ1 e he heN
  linarith [hsd, htail, hsum]

/-!
## Discharging Parseval — the total-probability normalisation `hsum`

The remaining piece of N&C §5.35 is the completeness hypothesis `hsum` used by
`qpeSuccessBound`: that the readout probabilities `‖qpeAmp‖²` sum to `1` over one full
period.  This is **not** an external quantum-mechanical input — it is the discrete Fourier
/ character orthogonality (Parseval) identity, provable as pure mathematics.  We prove it
below (`qpeAmp_parseval`) and use it to state the headline bound with no hypotheses at all
(`qpeSuccessBound_unconditional`).
-/

/-- Auxiliary unit-circle phase `cexp x = exp(x·i)` for real `x`.  Every exponential in
`qpeAmp` is of this form, and packaging it lets us reason with clean algebra
(`cexp_add`, `cexp_conj`, `cexp_pow`). -/
private noncomputable def cexp (x : ℝ) : ℂ := Complex.exp ((x : ℝ) * Complex.I)

private lemma cexp_add (x y : ℝ) : cexp x * cexp y = cexp (x + y) := by
  simp only [cexp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma cexp_zero : cexp 0 = 1 := by
  simp [cexp]

private lemma cexp_conj (x : ℝ) : (starRingEnd ℂ) (cexp x) = cexp (-x) := by
  simp only [cexp]
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma cexp_pow (x : ℝ) (n : ℕ) : cexp x ^ n = cexp ((n : ℝ) * x) := by
  simp only [cexp]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Character orthogonality on one period.**  For an integer frequency `d` with
`|d| < N`, the sum of the `N`-th–root-of-unity characters `exp(2πi·d·j/N)` over the window
`[1 − N/2, N/2]` (which has exactly `N` integers when `N` is even) is `N` if `d = 0` and `0`
otherwise.  This is the discrete orthogonality relation underlying Parseval; the `d ≠ 0`
case is a geometric series with ratio `exp(2πi·d/N) ≠ 1` whose `N`-th power is
`exp(2πi·d) = 1`. -/
private lemma charSum_eq (N : ℕ) (hEven : Even N) (hN : 0 < N) (d : ℤ)
    (hd : d.natAbs < N) :
    ∑ j ∈ Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) ((N / 2 : ℕ) : ℤ),
      cexp (2 * Real.pi * ((d : ℝ) * (j : ℝ) / N)) = if d = 0 then (N : ℂ) else 0 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNr
  have hNN : 2 * (N / 2) = N := Nat.two_mul_div_two_of_even hEven
  by_cases hd0 : d = 0
  · subst hd0
    rw [if_pos rfl]
    have hcng : ∀ j ∈ Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) ((N / 2 : ℕ) : ℤ),
        cexp (2 * Real.pi * (((0 : ℤ) : ℝ) * (j : ℝ) / N)) = 1 := by
      intro j _
      simp only [Int.cast_zero, zero_mul, zero_div, mul_zero]
      exact cexp_zero
    rw [Finset.sum_congr rfl hcng, Finset.sum_const]
    have hcard : (Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) ((N / 2 : ℕ) : ℤ)).card = N := by
      rw [Int.card_Icc]; omega
    rw [hcard, nsmul_eq_mul, mul_one]
  · rw [if_neg hd0]
    set a : ℤ := 1 - ((N / 2 : ℕ) : ℤ) with ha
    have hd0r : (d : ℝ) / N ≠ 0 := div_ne_zero (by exact_mod_cast hd0) hNne
    have hdabs : |(d : ℝ)| < N := by
      rw [abs_lt]
      refine ⟨?_, ?_⟩
      · have : -(N : ℤ) < d := by omega
        exact_mod_cast this
      · have : d < (N : ℤ) := by omega
        exact_mod_cast this
    have hd1 : |(d : ℝ) / N| < 1 := by
      rw [abs_div, abs_of_pos hNr, div_lt_one hNr]; exact hdabs
    have hωne : cexp (2 * Real.pi * ((d : ℝ) / N)) ≠ 1 := by
      exact exp_phase_ne_one ((d : ℝ) / N) hd0r hd1
    have hωN : cexp (2 * Real.pi * ((d : ℝ) / N)) ^ N = 1 := by
      rw [cexp_pow]
      have harg : (N : ℝ) * (2 * Real.pi * ((d : ℝ) / N)) = 2 * Real.pi * (d : ℝ) := by
        field_simp
      rw [harg]
      simp only [cexp]
      rw [show ((2 * Real.pi * (d : ℝ) : ℝ) : ℂ) * Complex.I
            = (d : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I d
    have hreindex : ∑ j ∈ Finset.Icc a ((N / 2 : ℕ) : ℤ),
          cexp (2 * Real.pi * ((d : ℝ) * (j : ℝ) / N))
        = cexp (2 * Real.pi * ((d : ℝ) * (a : ℝ) / N))
            * ∑ i ∈ Finset.range N, cexp (2 * Real.pi * ((d : ℝ) / N)) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_nbij' (fun (j : ℤ) => (j - a).toNat) (fun (i : ℕ) => a + (i : ℤ))
      · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
      · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Icc]; omega
      · intro j hj; rw [Finset.mem_Icc] at hj; omega
      · intro i hi; rw [Finset.mem_range] at hi; omega
      · intro j hj
        rw [Finset.mem_Icc] at hj
        rw [cexp_pow, cexp_add]
        congr 1
        have hjm : (((j - a).toNat : ℕ) : ℝ) = (j : ℝ) - (a : ℝ) := by
          have h1 : ((j - a).toNat : ℤ) = j - a := Int.toNat_of_nonneg (by omega)
          have h2 : (((j - a).toNat : ℕ) : ℝ) = (((j - a).toNat : ℤ) : ℝ) := by push_cast; ring
          rw [h2, h1]; push_cast; ring
        rw [hjm]; ring
    rw [hreindex, geom_sum_eq hωne N, hωN]
    simp

/-- **Per-outcome cross term.**  Fixing register indices `k, k' < N`, the sum over the
period of `exp(2πi·k·Δⱼ)·conj(exp(2πi·k'·Δⱼ))` (with `Δⱼ = (j − δ)/N`) collapses, by
`charSum_eq`, to `N` on the diagonal `k = k'` and `0` off it: the `δ`-dependent phase is
constant in `j` and factors out, leaving the pure character orthogonality sum. -/
private lemma innerSum_eq (N : ℕ) (hEven : Even N) (hN : 0 < N) (δ : ℝ) (k k' : ℕ)
    (hk : k < N) (hk' : k' < N) :
    ∑ j ∈ Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) ((N / 2 : ℕ) : ℤ),
      cexp (2 * Real.pi * ((k : ℝ) * (((j : ℝ) - δ) / N)))
        * cexp (-(2 * Real.pi * ((k' : ℝ) * (((j : ℝ) - δ) / N))))
      = if k = k' then (N : ℂ) else 0 := by
  have hd : ((k : ℤ) - (k' : ℤ)).natAbs < N := by omega
  have hstep : ∀ j ∈ Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) ((N / 2 : ℕ) : ℤ),
      cexp (2 * Real.pi * ((k : ℝ) * (((j : ℝ) - δ) / N)))
        * cexp (-(2 * Real.pi * ((k' : ℝ) * (((j : ℝ) - δ) / N))))
      = cexp (2 * Real.pi * ((((k : ℤ) - (k' : ℤ) : ℤ) : ℝ) * (j : ℝ) / N))
        * cexp (-(2 * Real.pi * ((((k : ℤ) - (k' : ℤ) : ℤ) : ℝ) * δ / N))) := by
    intro j _
    rw [cexp_add, cexp_add]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul,
    charSum_eq N hEven hN ((k : ℤ) - (k' : ℤ)) hd]
  by_cases hkk : k = k'
  · subst hkk
    rw [sub_self, if_pos rfl, if_pos rfl]
    simp only [Int.cast_zero, zero_mul, zero_div, mul_zero, neg_zero, cexp_zero, mul_one]
  · have hdne : (k : ℤ) - (k' : ℤ) ≠ 0 := by omega
    rw [if_neg hdne, if_neg hkk, zero_mul]

/-- **N&C (5.35), Parseval / total probability.**  Over one full period of outcomes
`j ∈ [1 − N/2, N/2]` (exactly `N` of them, since `N` is even) the QPE readout probabilities
`‖qpeAmp N ((j − δ)/N)‖²` sum to `1`.  This is proved as pure mathematics — it is the
discrete Fourier unitarity / character-orthogonality identity (`charSum_eq`) — and requires
no quantum-mechanical or semantic input.  It is exactly the hypothesis `hsum` demanded by
`qpeSuccessBound`; see `qpeSuccessBound_unconditional`. -/
theorem qpeAmp_parseval (N : ℕ) (hEven : Even N) (hN : 0 < N) (δ : ℝ) :
    ∑ j ∈ Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) ((N / 2 : ℕ) : ℤ),
      ‖qpeAmp N (((j : ℝ) - δ) / N)‖ ^ 2 = 1 := by
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hAexp : ∀ j : ℤ, qpeAmp N (((j : ℝ) - δ) / N)
      = (1 / (N : ℂ)) * ∑ k ∈ Finset.range N,
          cexp (2 * Real.pi * ((k : ℝ) * (((j : ℝ) - δ) / N))) := by
    intro j; simp only [qpeAmp, cexp]
  have hconj : ∀ j : ℤ, (starRingEnd ℂ) (qpeAmp N (((j : ℝ) - δ) / N))
      = (1 / (N : ℂ)) * ∑ k ∈ Finset.range N,
          cexp (-(2 * Real.pi * ((k : ℝ) * (((j : ℝ) - δ) / N)))) := by
    intro j
    rw [hAexp]
    simp only [map_mul, map_sum, map_div₀, map_one, Complex.conj_natCast, cexp_conj]
  have hterm : ∀ j : ℤ, ((‖qpeAmp N (((j : ℝ) - δ) / N)‖ ^ 2 : ℝ) : ℂ)
      = qpeAmp N (((j : ℝ) - δ) / N) * (starRingEnd ℂ) (qpeAmp N (((j : ℝ) - δ) / N)) := by
    intro j; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hbig : ∀ j : ℤ,
      qpeAmp N (((j : ℝ) - δ) / N) * (starRingEnd ℂ) (qpeAmp N (((j : ℝ) - δ) / N))
      = (1 / (N : ℂ)) ^ 2 * ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N,
          cexp (2 * Real.pi * ((k : ℝ) * (((j : ℝ) - δ) / N)))
            * cexp (-(2 * Real.pi * ((k' : ℝ) * (((j : ℝ) - δ) / N)))) := by
    intro j
    rw [hconj j, hAexp j, mul_mul_mul_comm, ← pow_two, Finset.sum_mul_sum]
  have hinner : ∀ k ∈ Finset.range N,
      (∑ k' ∈ Finset.range N, (if k = k' then (N : ℂ) else 0)) = (N : ℂ) := by
    intro k hk
    rw [Finset.sum_eq_single k
      (fun k' _ hne => if_neg (fun h => hne h.symm)) (fun h => absurd hk h)]
    exact if_pos rfl
  have main : ((∑ j ∈ Finset.Icc (1 - ((N / 2 : ℕ) : ℤ)) ((N / 2 : ℕ) : ℤ),
      ‖qpeAmp N (((j : ℝ) - δ) / N)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    rw [Finset.sum_congr rfl (fun j _ => hbig j)]
    rw [← Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun k' hk' =>
      innerSum_eq N hEven hN δ k k' (Finset.mem_range.mp hk) (Finset.mem_range.mp hk')))]
    rw [Finset.sum_congr rfl hinner]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  exact_mod_cast main

/-- **N&C (5.35), the headline precision bound — unconditional form.**  The probability of
measuring within `e` of the true value is at least `1 − 1/(2(e−1))`, with **no** Parseval
hypothesis: the completeness of the readout distribution is discharged internally by
`qpeAmp_parseval`.  This is the fully self-contained statement of the QPE precision
guarantee — as a statement about the amplitude function `qpeAmp` only, not about any
program's measurement distribution. -/
theorem qpeSuccessBound_unconditional (N : ℕ) (hEven : Even N) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (e : ℕ) (he : 2 ≤ e) (heN : 2 * e < N) :
    (1 : ℝ) - 1 / (2 * ((e : ℝ) - 1)) ≤
      ∑ j ∈ Finset.Icc (-(e : ℤ)) (e : ℤ), ‖qpeAmp N (((j : ℝ) - δ) / N)‖ ^ 2 :=
  qpeSuccessBound N hEven δ hδ0 hδ1 e he heN (qpeAmp_parseval N hEven (by omega) δ)

/-! ## Conjugation symmetry and the binary product form of the geometric amplitude -/

/-- Flipping the sign of the offset conjugates the geometric amplitude:
`qpeAmp N (-Δ) = conj (qpeAmp N Δ)`.  Each phase `e^{2πikΔ}` conjugates to `e^{-2πikΔ}`. -/
theorem qpeAmp_neg (N : ℕ) (Δ : ℝ) :
    qpeAmp N (-Δ) = (starRingEnd ℂ) (qpeAmp N Δ) := by
  unfold qpeAmp
  rw [map_mul, map_sum]
  have hconjN : (starRingEnd ℂ) (1 / (N : ℂ)) = 1 / (N : ℂ) := by
    rw [map_div₀, map_one, Complex.conj_natCast]
  rw [hconjN]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Norm form of the conjugation symmetry: `‖qpeAmp N (-Δ)‖ = ‖qpeAmp N Δ‖`. -/
theorem norm_qpeAmp_neg (N : ℕ) (Δ : ℝ) :
    ‖qpeAmp N (-Δ)‖ = ‖qpeAmp N Δ‖ := by
  rw [qpeAmp_neg, RCLike.norm_conj]

/-- **Product form.**  At `N = 2 ^ t` the geometric amplitude factorises over the `t`
binary wires: `qpeAmp (2 ^ t) Δ = ∏_{j<t} (1 + e^{2πi·2^j·Δ})/2`.  Proved by induction on
`t`, splitting `range (2^(t+1))` into its lower and upper halves. -/
theorem qpeAmp_two_pow_prod (t : ℕ) (Δ : ℝ) :
    qpeAmp (2 ^ t) Δ =
      ∏ j ∈ Finset.range t,
        ((1 + Complex.exp ((2 * Real.pi * ((2 : ℝ) ^ j * Δ) : ℝ) * Complex.I)) / 2) := by
  induction t with
  | zero =>
    simp only [pow_zero, Finset.range_zero, Finset.prod_empty]
    unfold qpeAmp
    simp
  | succ t ih =>
    unfold qpeAmp
    rw [show (2 : ℕ) ^ (t + 1) = 2 ^ t + 2 ^ t by ring, Finset.sum_range_add]
    -- rewrite the upper-half sum as a phase times the lower-half sum
    have hupper : ∑ k ∈ Finset.range (2 ^ t),
          Complex.exp ((2 * Real.pi * (((2 ^ t + k : ℕ) : ℝ) * Δ) : ℝ) * Complex.I)
        = Complex.exp ((2 * Real.pi * (((2 : ℝ) ^ t) * Δ) : ℝ) * Complex.I) *
            ∑ k ∈ Finset.range (2 ^ t),
              Complex.exp ((2 * Real.pi * ((k : ℝ) * Δ) : ℝ) * Complex.I) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hupper]
    -- factor the total sum
    have hfactor : (1 / ((2 ^ t + 2 ^ t : ℕ) : ℂ)) *
          ((∑ k ∈ Finset.range (2 ^ t),
              Complex.exp ((2 * Real.pi * ((k : ℝ) * Δ) : ℝ) * Complex.I)) +
            Complex.exp ((2 * Real.pi * (((2 : ℝ) ^ t) * Δ) : ℝ) * Complex.I) *
              ∑ k ∈ Finset.range (2 ^ t),
                Complex.exp ((2 * Real.pi * ((k : ℝ) * Δ) : ℝ) * Complex.I))
        = ((1 + Complex.exp ((2 * Real.pi * (((2 : ℝ) ^ t) * Δ) : ℝ) * Complex.I)) / 2) *
            ((1 / ((2 ^ t : ℕ) : ℂ)) *
              ∑ k ∈ Finset.range (2 ^ t),
                Complex.exp ((2 * Real.pi * ((k : ℝ) * Δ) : ℝ) * Complex.I)) := by
      have h2t : ((2 ^ t : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (pow_ne_zero t two_ne_zero)
      have hcast : ((2 ^ t + 2 ^ t : ℕ) : ℂ) = ((2 ^ t : ℕ) : ℂ) + ((2 ^ t : ℕ) : ℂ) := by
        push_cast; ring
      rw [hcast, ← two_mul]
      generalize (∑ k ∈ Finset.range (2 ^ t),
          Complex.exp ((2 * Real.pi * ((k : ℝ) * Δ) : ℝ) * Complex.I)) = S
      generalize (Complex.exp ((2 * Real.pi * (((2 : ℝ) ^ t) * Δ) : ℝ) * Complex.I)) = E
      field_simp
    rw [hfactor,
      show (1 / ((2 ^ t : ℕ) : ℂ)) *
          (∑ k ∈ Finset.range (2 ^ t),
            Complex.exp ((2 * Real.pi * ((k : ℝ) * Δ) : ℝ) * Complex.I))
        = qpeAmp (2 ^ t) Δ from rfl,
      ih, Finset.prod_range_succ, mul_comm]

end Qhl
