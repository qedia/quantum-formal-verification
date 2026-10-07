import Qhl.Register.Qubits
import Qhl.Gate.Phase
import Qhl.Logic.Frame
import Qhl.Foundations.BigOps
import Qhl.Foundations.UnitNorm

/-!
# The Fourier state of the standard `n`-qubit world

The postcondition profile of the quantum Fourier transform, packaged as a named
state of the standard `n`-qubit world `QubitL n = Fin n`
(`Qhl/Register/Qubits.lean`). This is the Lean counterpart of CoqQ's `QFTbv`
(`src/qtype.v:958`) together with `QFTbvTE` (`qtype.v:1006`) / `QFTbv_rev`
(`src/example/coqq_paper/example.v:299`).

* `natVal x` — the value `∑ᵢ xᵢ·2^(n-1-i)` of a **big-endian** bit vector (bit
  `0` most significant); CoqQ `bseq2nat`/`bseq2ord`.
* `qftAngle x i` — the angle `2π·0.xᵢ xᵢ₊₁ … xₙ₋₁` of the `i`-th output wire;
  CoqQ `bitstr2rat (drop i sb)` (`qtype.v:817`) scaled by `2π`.
* `finTarget hi j` — the `j`-th cell strictly after cell `i`, the target family
  of the QFT's controlled-phase ladder, together with
  `qftAngle_eq_head_add_ladder`, which splits `qftAngle x i` into the Hadamard
  head `xᵢ·π` and the ladder `∑ⱼ x_{i+1+j}·2π/2^(j+2)` — exactly the shape the
  QFT derivation accumulates.
* `fourierState n x` — the genuine DFT profile, with amplitude
  `2^{-n/2}·e^{2πi·natVal x·natVal y/2^n}` at the computational basis state `y`
  (CoqQ `QFTbv`).
* `fourierState_eq_prodV` — **the headline**: the DFT state *is* the product of
  phase kets `⊗ⱼ 'ph (2π·0.x_{n-1-j} … x_{n-1})` (CoqQ `QFTbv_rev`). Its
  arithmetic core is `qftAngle_sum_eq`, which matches the two exponents modulo
  `2π`.
* `norm_fourierState` — the Fourier state is a unit vector, read off the product
  form.

On top of that DFT core the file carries the **stage algebra** the QFT-style
derivations run on — the loop invariants themselves, so that an example is left
with nothing but its programs and its triples (§7–§9):

* `qftLadderSum x m` — the phase a controlled-phase ladder has accumulated after
  `m` of its rungs, with its `zero`/`full`/`succ` laws read off the guarded-sum
  toolkit `Qhl/Foundations/BigOps.lean` (mathcomp `big_ord_recr`).
* `qftLadderFam` — the invariant family of one ladder, at an **arbitrary** world
  `L` and control cell `c`, with its endpoint identities and its one-rung update
  step `qftLadderFam_step`.
* `qftStageFam` / `qftStageMid` — the invariant of the QFT's outer loop (first
  `m` wires already Fourier-phased) and its mid-stage form (the Hadamard has
  fired, the ladder has not), with `qftStageMid_step` folding one whole stage.
* `revIdx`, `revA`, `revB` — the wires of the reversal network (CoqQ `rev_ord`
  and the `rev_circuit` transpositions, `example.v:140`) and `qftRevFam`, the
  invariant "the outermost `m` pairs are already swapped", with its endpoints
  and its one-swap step.

Nothing here mentions a program: this file is pure state algebra, reusable by
the QFT, inverse-QFT and phase-estimation examples.
-/

namespace Qhl

open Finset

/-! ## §1. The value of a big-endian bit vector -/

/-- The value `∑ᵢ xᵢ·2^(n-1-i)` of the bit vector `x` read **big-endian**: bit
`0` is the most significant one. CoqQ `bseq2nat`/`bseq2ord` (`qtype.v`). -/
def natVal {n : ℕ} (x : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, (if x i then 1 else 0) * 2 ^ (n - 1 - (i : ℕ))

/-- `natVal` in `ℝ`, with the bits presented by `bitVal`. -/
theorem natVal_cast {n : ℕ} (x : Fin n → Bool) :
    ((natVal x : ℕ) : ℝ) = ∑ i : Fin n, bitVal (x i) * 2 ^ (n - 1 - (i : ℕ)) := by
  rw [natVal, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases x i <;> simp [bitVal]

/-! ## §2. The QFT angle of a wire -/

/-- The angle carried by the `i`-th output wire of the quantum Fourier
transform: `2π · 0.xᵢ xᵢ₊₁ … xₙ₋₁` read as a binary fraction, i.e.
`2π · ∑_{t ≥ i} xₜ · 2^{-(t-i+1)}` — the bit `xᵢ` contributes the half turn,
`x_{i+1}` the quarter turn, and so on. CoqQ `bitstr2rat (drop i sb)`
(`qtype.v:817`), whose value is this angle divided by `2π`. -/
noncomputable def qftAngle {n : ℕ} (x : Fin n → Bool) (i : ℕ) : ℝ :=
  ∑ t : Fin n, if i ≤ (t : ℕ) then bitVal (x t) * (2 * Real.pi / 2 ^ ((t : ℕ) - i + 1)) else 0

/-! ## §3. The controlled-phase ladder of one QFT stage -/

/-- The `j`-th cell strictly after cell `i` of an `n`-cell world: the target
family of the controlled-phase ladder that the `i`-th QFT stage runs. CoqQ's
`s.[i + j.+1]` in the inner loop of `QuantumFourierTransform`
(`example/coqq_paper/example.v:164`). -/
def finTarget {n i : ℕ} (hi : i < n) (j : Fin (n - 1 - i)) : Fin n :=
  ⟨i + 1 + (j : ℕ), by omega⟩

/-- The underlying index of `finTarget`. -/
@[simp]
theorem finTarget_val {n i : ℕ} (hi : i < n) (j : Fin (n - 1 - i)) :
    ((finTarget hi j : Fin n) : ℕ) = i + 1 + (j : ℕ) := rfl

/-- Distinct ladder positions name distinct cells. -/
theorem finTarget_injective {n i : ℕ} (hi : i < n) : Function.Injective (finTarget hi) := by
  intro a b hab
  rw [Fin.ext_iff, finTarget_val, finTarget_val] at hab
  exact Fin.ext (by omega)

/-- No ladder target is the stage's own control cell. -/
theorem finTarget_ne {n i : ℕ} (hi : i < n) (j : Fin (n - 1 - i)) :
    finTarget hi j ≠ ⟨i, hi⟩ := by
  intro h
  have h' : i + 1 + (j : ℕ) = i := congrArg Fin.val h
  omega

/-- **The head + ladder decomposition of a QFT angle.** The wire `i` picks up
the half turn `xᵢ·π` from its Hadamard, and then the turn `2π/2^(j+2)` from the
`j`-th controlled phase of the ladder, controlled by the cell `finTarget hi j`.
This is the exact shape the QFT derivation accumulates, matched against the
closed form `qftAngle`. -/
theorem qftAngle_eq_head_add_ladder {n : ℕ} (x : Fin n → Bool) {i : ℕ} (hi : i < n) :
    qftAngle x i
      = bitVal (x ⟨i, hi⟩) * Real.pi
        + ∑ j : Fin (n - 1 - i),
            bitVal (x (finTarget hi j)) * (2 * Real.pi / 2 ^ ((j : ℕ) + 2)) := by
  have hset : (univ.filter fun t : Fin n => i ≤ (t : ℕ))
      = insert (⟨i, hi⟩ : Fin n) (univ.image (finTarget hi)) := by
    ext t
    rw [mem_filter, mem_insert, mem_image]
    constructor
    · rintro ⟨-, ht⟩
      rcases eq_or_lt_of_le ht with h' | h'
      · exact Or.inl (Fin.ext h'.symm)
      · refine Or.inr ⟨⟨(t : ℕ) - i - 1, by omega⟩, mem_univ _, Fin.ext ?_⟩
        change i + 1 + ((t : ℕ) - i - 1) = (t : ℕ)
        omega
    · rintro (rfl | ⟨j, -, rfl⟩)
      · exact ⟨mem_univ _, le_rfl⟩
      · refine ⟨mem_univ _, ?_⟩
        change i ≤ i + 1 + (j : ℕ)
        omega
  have hnot : (⟨i, hi⟩ : Fin n) ∉ univ.image (finTarget hi) := by
    simp only [mem_image, not_exists]
    rintro j ⟨-, hj⟩
    exact finTarget_ne hi j hj
  rw [qftAngle, ← Finset.sum_filter, hset, Finset.sum_insert hnot,
    Finset.sum_image fun a _ b _ h => finTarget_injective hi h]
  congr 1
  · norm_num
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((finTarget hi j : Fin n) : ℕ) - i + 1 = (j : ℕ) + 2 by simp; omega]

/-! ## §4. The arithmetic core: DFT exponent = phase-ket exponent, mod `2π` -/

/-- The pairing identity behind `qftAngle_sum_eq`, for one pair of bit
positions `(t, j)`. The DFT contribution of the `x`-bit at `t` against the
`y`-bit at `j` either lands *inside* the binary fraction of wire `n-1-j` (when
`n-1-j ≤ t`), or is a whole number of turns (when `t` is too small), and in that
case it contributes the integer `2^(n-2-t-j)`. Both branches are pure algebra:
the bit values `a` and `b` are arbitrary reals. -/
theorem qft_pair_eq {n : ℕ} (a b : ℝ) {t j : ℕ} (ht : t < n) (hj : j < n) :
    2 * Real.pi * (a * 2 ^ (n - 1 - t)) * (b * 2 ^ (n - 1 - j)) / 2 ^ n
      = (if n - 1 - j ≤ t then b * (a * (2 * Real.pi / 2 ^ (t - (n - 1 - j) + 1))) else 0)
        + (if n - 1 - j ≤ t then 0 else a * b * 2 ^ (n - 2 - t - j)) * (2 * Real.pi) := by
  by_cases h : n - 1 - j ≤ t
  · rw [if_pos h, if_pos h, zero_mul, add_zero]
    have hp : (n - 1 - t) + (n - 1 - j) + (t - (n - 1 - j) + 1) = n := by omega
    have key : (2 : ℝ) ^ (n - 1 - t) * 2 ^ (n - 1 - j) * 2 ^ (t - (n - 1 - j) + 1) = 2 ^ n := by
      rw [← pow_add, ← pow_add, hp]
    rw [div_eq_iff (by positivity : (2 : ℝ) ^ n ≠ 0), ← key]
    field_simp
  · rw [if_neg h, if_neg h, zero_add]
    have hp : (n - 1 - t) + (n - 1 - j) = (n - 2 - t - j) + n := by omega
    have key : (2 : ℝ) ^ (n - 1 - t) * 2 ^ (n - 1 - j) = 2 ^ (n - 2 - t - j) * 2 ^ n := by
      rw [← pow_add, ← pow_add, hp]
    rw [div_eq_iff (by positivity : (2 : ℝ) ^ n ≠ 0)]
    linear_combination (2 * Real.pi * a * b) * key

/-- **The exponent congruence.** The DFT phase `2π·natVal x·natVal y/2^n` and
the total phase `∑ⱼ yⱼ · qftAngle x (n-1-j)` collected by the product of phase
kets agree **modulo `2π`**: they differ by the integer number of turns
`∑_{t+j ≤ n-2} xₜ·yⱼ·2^(n-2-t-j)`. This is the whole content of CoqQ's
`QFTbvTE` computation (`qtype.v:1006`). -/
theorem qftAngle_sum_eq (n : ℕ) (x y : Fin n → Bool) :
    ∃ N : ℤ,
      2 * Real.pi * (natVal x * natVal y : ℕ) / 2 ^ n
        = (∑ j : Fin n, bitVal (y j) * qftAngle x (n - 1 - (j : ℕ))) + N * (2 * Real.pi) := by
  classical
  refine ⟨((∑ j : Fin n, ∑ t : Fin n,
      if n - 1 - (j : ℕ) ≤ (t : ℕ) then 0
      else (if x t then 1 else 0) * (if y j then 1 else 0)
        * 2 ^ (n - 2 - (t : ℕ) - (j : ℕ)) : ℕ) : ℤ), ?_⟩
  have hlhs : 2 * Real.pi * ((natVal x * natVal y : ℕ) : ℝ) / 2 ^ n
      = ∑ j : Fin n, ∑ t : Fin n,
          2 * Real.pi * (bitVal (x t) * 2 ^ (n - 1 - (t : ℕ)))
            * (bitVal (y j) * 2 ^ (n - 1 - (j : ℕ))) / 2 ^ n := by
    rw [Nat.cast_mul, natVal_cast, natVal_cast, Finset.sum_mul_sum, Finset.sum_comm]
    simp only [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hK : (((∑ j : Fin n, ∑ t : Fin n,
        if n - 1 - (j : ℕ) ≤ (t : ℕ) then 0
        else (if x t then 1 else 0) * (if y j then 1 else 0)
          * 2 ^ (n - 2 - (t : ℕ) - (j : ℕ)) : ℕ) : ℤ) : ℝ)
      = ∑ j : Fin n, ∑ t : Fin n,
          (if n - 1 - (j : ℕ) ≤ (t : ℕ) then 0
           else bitVal (x t) * bitVal (y j) * 2 ^ (n - 2 - (t : ℕ) - (j : ℕ))) := by
    rw [Int.cast_natCast, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : n - 1 - (j : ℕ) ≤ (t : ℕ)
    · rw [if_pos h, if_pos h, Nat.cast_zero]
    · rw [if_neg h, if_neg h]
      cases x t <;> cases y j <;> push_cast <;> simp [bitVal]
  have hrhs : (∑ j : Fin n, bitVal (y j) * qftAngle x (n - 1 - (j : ℕ)))
        + (∑ j : Fin n, ∑ t : Fin n,
            (if n - 1 - (j : ℕ) ≤ (t : ℕ) then 0
             else bitVal (x t) * bitVal (y j) * 2 ^ (n - 2 - (t : ℕ) - (j : ℕ))))
          * (2 * Real.pi)
      = ∑ j : Fin n, ∑ t : Fin n,
          ((if n - 1 - (j : ℕ) ≤ (t : ℕ)
              then bitVal (y j) * (bitVal (x t)
                * (2 * Real.pi / 2 ^ ((t : ℕ) - (n - 1 - (j : ℕ)) + 1)))
              else 0)
            + (if n - 1 - (j : ℕ) ≤ (t : ℕ) then 0
               else bitVal (x t) * bitVal (y j) * 2 ^ (n - 2 - (t : ℕ) - (j : ℕ)))
              * (2 * Real.pi)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [qftAngle, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    split <;> simp
  rw [hlhs, hK, hrhs]
  exact Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun t _ => qft_pair_eq _ _ t.isLt j.isLt

/-! ## §5. The Fourier state -/

/-- The coordinates of a phase state in exponential form: every coordinate is
`e^{i·b·θ}/√2`. -/
theorem phaseKet_apply_exp (θ : ℝ) (c : Bool) :
    phaseKet θ c = (Real.sqrt 2 : ℂ)⁻¹ * Complex.exp (((bitVal c * θ : ℝ) : ℂ) * Complex.I) := by
  cases c <;> simp [phaseKet_apply, bitVal]

/-- **The Fourier state** of the big-endian bit vector `x` on the standard
`n`-qubit world: the discrete Fourier profile with amplitude
`2^{-n/2}·e^{2πi·natVal x·natVal y/2^n}` at the computational basis state `y`.
CoqQ `QFTbv sb` (`qtype.v:958`). -/
noncomputable def fourierState (n : ℕ) (x : Fin n → Bool) :
    HS (QubitD n) (univ : Finset (QubitL n)) :=
  WithLp.toLp 2 fun l =>
    ((Real.sqrt 2 : ℂ))⁻¹ ^ n
      * Complex.exp (((2 * Real.pi
          * ((natVal x * natVal fun i : QubitL n => l ⟨i, Finset.mem_univ i⟩ : ℕ) : ℝ)
          / 2 ^ n : ℝ) : ℂ) * Complex.I)

/-- The coordinates of the Fourier state. -/
@[simp]
theorem fourierState_apply (n : ℕ) (x : Fin n → Bool)
    (l : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    fourierState n x l
      = ((Real.sqrt 2 : ℂ))⁻¹ ^ n
        * Complex.exp (((2 * Real.pi
            * ((natVal x * natVal fun i : QubitL n => l ⟨i, Finset.mem_univ i⟩ : ℕ) : ℝ)
            / 2 ^ n : ℝ) : ℂ) * Complex.I) := rfl

/-- **The product form of the Fourier state** (CoqQ `QFTbv_rev`,
`example/coqq_paper/example.v:299`): the discrete Fourier profile of `x` is the
product state whose `j`-th factor is the phase ket of angle
`2π·0.x_{n-1-j} … x_{n-1}`. This is the theorem that turns the QFT's
wire-by-wire postcondition into the genuine Fourier state, and back. -/
theorem fourierState_eq_prodV (n : ℕ) (x : Fin n → Bool) :
    fourierState n x
      = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (fun j => phaseKet (qftAngle x (n - 1 - (j : ℕ)))) := by
  refine PiLp.ext fun l => ?_
  set y : Fin n → Bool := fun i : QubitL n => l ⟨i, Finset.mem_univ i⟩ with hy
  rw [fourierState_apply, prodV_apply]
  have hcard : Fintype.card ↥(univ : Finset (QubitL n)) = n := by simp
  have hsum : ∑ i : ↥(univ : Finset (QubitL n)),
        (((bitVal (l i) * qftAngle x (n - 1 - ((i : QubitL n) : ℕ)) : ℝ)) : ℂ) * Complex.I
      = (((∑ j : Fin n, bitVal (y j) * qftAngle x (n - 1 - (j : ℕ)) : ℝ)) : ℂ) * Complex.I := by
    rw [← Finset.sum_mul, ← Complex.ofReal_sum]
    congr 2
    exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun a : QubitL n => Finset.mem_univ a)
      _ _ fun i => rfl
  have hprod : (∏ i : ↥(univ : Finset (QubitL n)),
        phaseKet (qftAngle x (n - 1 - ((i : QubitL n) : ℕ))) (l i))
      = ((Real.sqrt 2 : ℂ))⁻¹ ^ n
        * Complex.exp ((((∑ j : Fin n,
            bitVal (y j) * qftAngle x (n - 1 - (j : ℕ)) : ℝ)) : ℂ) * Complex.I) := by
    rw [Finset.prod_congr rfl fun (i : ↥(univ : Finset (QubitL n))) _ => phaseKet_apply_exp
        (qftAngle x (n - 1 - ((i : QubitL n) : ℕ))) (l i),
      Finset.prod_mul_distrib, Finset.prod_const, ← Complex.exp_sum, hsum, Finset.card_univ,
      hcard]
  rw [hprod]
  obtain ⟨N, hN⟩ := qftAngle_sum_eq n x y
  rw [hN, show (((∑ j : Fin n, bitVal (y j) * qftAngle x (n - 1 - (j : ℕ)))
        + (N : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I
      = (((∑ j : Fin n, bitVal (y j) * qftAngle x (n - 1 - (j : ℕ)) : ℝ)) : ℂ) * Complex.I
        + (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The Fourier state is a unit vector: it is a product of phase kets, each of
which is one. CoqQ `QFTbv_onb` (`qtype.v:969`) at equal arguments. -/
@[simp]
theorem norm_fourierState (n : ℕ) (x : Fin n → Bool) : ‖fourierState n x‖ = 1 := by
  rw [fourierState_eq_prodV]
  exact norm_prodV_eq_one _ fun _ => norm_phaseKet _

/-- The Fourier state of the all-zero bit vector is the uniform superposition
`⊗ᵢ ∣+⟩`: every phase is trivial. CoqQ `QFTbv_uniform` (`qtype.v:986`). -/
theorem fourierState_false_eq_allPlus (n : ℕ) :
    fourierState n (fun _ => false) = allPlus n := by
  refine PiLp.ext fun l => ?_
  rw [fourierState_apply, allPlus_apply]
  norm_num [natVal]

/-! ## §6. Smoke checks -/

example : natVal ![true, false] = 2 := by decide

example : natVal ![true, true] = 3 := by decide

/-! ## §7. The guarded ladder phase

The accumulator of a controlled-phase ladder: after `m` of its `k` rungs the
control cell has picked up `∑_{j < m} xⱼ·2π/2^(j+2)`. Its three laws are the
guarded-sum toolkit of `Qhl/Foundations/BigOps.lean` (mathcomp `big_pred0`,
`big_ord_widen`, `big_ord_recr`) read at this summand. -/

/-- The phase a QFT controlled-phase ladder has accumulated after `m` of its `k`
rungs. The `m = k` value is the ladder half of `qftAngle_eq_head_add_ladder`. -/
noncomputable def qftLadderSum {k : ℕ} (x : Fin k → Bool) (m : ℕ) : ℝ :=
  ∑ j : Fin k, if (j : ℕ) < m then bitVal (x j) * (2 * Real.pi / 2 ^ ((j : ℕ) + 2)) else 0

/-- Before the first rung the ladder has accumulated nothing. -/
@[simp]
theorem qftLadderSum_zero {k : ℕ} (x : Fin k → Bool) : qftLadderSum x 0 = 0 :=
  sum_ite_lt_zero _

/-- After the last rung every bit has been absorbed. -/
theorem qftLadderSum_full {k : ℕ} (x : Fin k → Bool) :
    qftLadderSum x k = ∑ j : Fin k, bitVal (x j) * (2 * Real.pi / 2 ^ ((j : ℕ) + 2)) :=
  sum_ite_lt_of_le le_rfl _

/-- **One rung adds its own phase** — the arithmetic of every chain step of a
ladder loop, `big_ord_recr` at the ladder summand. -/
theorem qftLadderSum_succ {k : ℕ} (x : Fin k → Bool) {m : ℕ} (hm : m < k) :
    qftLadderSum x (m + 1)
      = qftLadderSum x m + bitVal (x ⟨m, hm⟩) * (2 * Real.pi / 2 ^ (m + 2)) :=
  sum_ite_lt_succ _ hm

/-! ## §8. The stage-invariant families

The loop invariants of the QFT derivations, as pure state algebra: each is a
family of qubit states indexed by the cells of the world, and each comes with
its two endpoint identities and the update step that one loop iteration
performs. No program, no triple and no proof rule occurs here. -/

section LadderFamily

variable {L : Type*} [DecidableEq L] (c : L) {k : ℕ} (x : Fin k → Bool) (φ₀ : ℝ)
  (ψ : ∀ _ : L, 𝕢)

/-- **The invariant of a controlled-phase ladder.** At stage `m` the control
cell `c` carries the phase `φ₀` advanced by the first `m` rungs; every other
cell is untouched. Stated at an arbitrary world `L` and control cell `c` — the
genericity that lets a single ladder triple be reused at every QFT stage and
every size (CoqQ `QFT_sub_cast`, `example/coqq_paper/example.v:176`). -/
noncomputable def qftLadderFam (m : ℕ) : ∀ _ : L, 𝕢 :=
  Function.update ψ c (phaseKet (φ₀ + qftLadderSum x m))

/-- Every cell of the ladder invariant is a unit vector. -/
theorem norm_qftLadderFam (hψ : ∀ i, ‖ψ i‖ = 1) (m : ℕ) (i : L) :
    ‖qftLadderFam c x φ₀ ψ m i‖ = 1 :=
  norm_update_unit_eq_one hψ (norm_phaseKet _) i

/-- The control cell of the ladder invariant. -/
@[simp]
theorem qftLadderFam_ctrl (m : ℕ) :
    qftLadderFam c x φ₀ ψ m c = phaseKet (φ₀ + qftLadderSum x m) :=
  Function.update_self _ _ _

/-- Every cell other than the control is untouched by the ladder invariant. -/
theorem qftLadderFam_of_ne {i : L} (h : i ≠ c) (m : ℕ) :
    qftLadderFam c x φ₀ ψ m i = ψ i :=
  Function.update_of_ne h _ _

/-- **Start of the ladder loop**: at stage `0` the invariant is the input family
itself, provided the control already carries the phase `'ph φ₀`. -/
theorem qftLadderFam_zero (hc : ψ c = phaseKet φ₀) : qftLadderFam c x φ₀ ψ 0 = ψ := by
  simp only [qftLadderFam, qftLadderSum_zero, add_zero, ← hc]
  exact Function.update_eq_self _ _

/-- **End of the ladder loop**: at stage `k` the control has absorbed the whole
ladder phase. -/
theorem qftLadderFam_full :
    qftLadderFam c x φ₀ ψ k
      = Function.update ψ c
          (phaseKet (φ₀ + ∑ j : Fin k, bitVal (x j) * (2 * Real.pi / 2 ^ ((j : ℕ) + 2)))) := by
  simp only [qftLadderFam, qftLadderSum_full]

/-- **One rung of the ladder loop.** Advancing the control's phase by the `j`-th
rung and rewriting the target back to its (unchanged) basis ket lands exactly on
the next stage of the invariant. This is the state-algebra content of a single
controlled-phase step; the gate content is `cphase_vpair_phaseKet`. -/
theorem qftLadderFam_step (j : Fin k) {t : L} (hct : c ≠ t) (ht : ψ t = qbit (x j)) :
    Function.update (Function.update (qftLadderFam c x φ₀ ψ (j : ℕ)) c
        (phaseKet (φ₀ + qftLadderSum x (j : ℕ)
          + bitVal (x j) * (2 * Real.pi / 2 ^ ((j : ℕ) + 2)))))
        t (qbit (x j))
      = qftLadderFam c x φ₀ ψ ((j : ℕ) + 1) := by
  funext i
  by_cases hi : i = t
  · rw [hi, Function.update_self, qftLadderFam_of_ne c x φ₀ ψ (Ne.symm hct)]
    exact ht.symm
  · rw [Function.update_of_ne hi]
    by_cases hc' : i = c
    · rw [hc', Function.update_self, qftLadderFam_ctrl, qftLadderSum_succ x j.isLt, add_assoc]
    · rw [Function.update_of_ne hc', qftLadderFam_of_ne c x φ₀ ψ hc',
        qftLadderFam_of_ne c x φ₀ ψ hc']

end LadderFamily

section StageFamily

variable (n : ℕ) (x : Fin n → Bool)

/-- **The invariant of the QFT's outer loop.** At stage `m` the first `m` wires
already carry their Fourier phase `'ph (qftAngle x i)`, the remaining ones still
carry their input bit `∣xᵢ⟩`. CoqQ's `QFT_iter` invariant
(`example/coqq_paper/example.v:167`). -/
noncomputable def qftStageFam (m : ℕ) (i : Fin n) : 𝕢 :=
  if (i : ℕ) < m then phaseKet (qftAngle x (i : ℕ)) else qbit (x i)

/-- Every wire of the stage invariant is a unit vector. -/
@[simp]
theorem norm_qftStageFam (m : ℕ) (i : Fin n) : ‖qftStageFam n x m i‖ = 1 := by
  simp [qftStageFam]

/-- **Start of the outer loop**: before any stage, every wire carries its input
bit. -/
theorem qftStageFam_zero : qftStageFam n x 0 = fun i => qbit (x i) := by
  funext i
  simp only [qftStageFam]
  rw [if_neg (Nat.not_lt_zero _)]

/-- **End of the outer loop**: after `n` stages every wire carries its Fourier
phase — the QFT profile up to the wire reversal. -/
theorem qftStageFam_full :
    qftStageFam n x n = fun i : Fin n => phaseKet (qftAngle x (i : ℕ)) := by
  funext i
  simp only [qftStageFam]
  rw [if_pos i.isLt]

/-- Its own wire is exactly the one stage `i` has not yet transformed. -/
theorem qftStageFam_self (i : Fin n) : qftStageFam n x (i : ℕ) i = qbit (x i) := by
  simp only [qftStageFam]
  rw [if_neg (lt_irrefl _)]

/-- **The mid-stage family**: the Hadamard of stage `i` has fired, its
controlled-phase ladder has not yet run. -/
noncomputable def qftStageMid (i : Fin n) : Fin n → 𝕢 :=
  Function.update (qftStageFam n x (i : ℕ)) i (phaseKet (bitVal (x i) * Real.pi))

/-- Every wire of the mid-stage family is a unit vector. -/
@[simp]
theorem norm_qftStageMid (i j : Fin n) : ‖qftStageMid n x i j‖ = 1 :=
  norm_update_unit_eq_one (norm_qftStageFam n x _) (norm_phaseKet _) j

/-- **The Hadamard half of a stage**: applying `H` to wire `i` of the stage
invariant produces the mid-stage family, since `H ∣b⟩ = 'ph (b·π)` (library
`H_qbit`, CoqQ `Hadamard_cb`). -/
theorem qftStageMid_eq_update_H (i : Fin n) :
    Function.update (qftStageFam n x (i : ℕ)) i
        ((H : 𝕢 →ₗ[ℂ] 𝕢) (qftStageFam n x (i : ℕ) i))
      = qftStageMid n x i := by
  rw [qftStageFam_self, H_qbit]
  rfl

/-- The control wire of the mid-stage family carries the Hadamard's half turn:
the ladder's initial phase `φ₀`. -/
@[simp]
theorem qftStageMid_self (i : Fin n) :
    qftStageMid n x i i = phaseKet (bitVal (x i) * Real.pi) :=
  Function.update_self _ _ _

/-- Every ladder target of stage `i` still carries its input bit: the targets
lie strictly after `i`, so no earlier stage has touched them. -/
theorem qftStageMid_target (i : Fin n) (j : Fin (n - 1 - (i : ℕ))) :
    qftStageMid n x i (finTarget i.isLt j) = qbit (x (finTarget i.isLt j)) := by
  have hv := finTarget_val i.isLt j
  have hne : finTarget i.isLt j ≠ i := finTarget_ne i.isLt j
  simp only [qftStageMid, Function.update_of_ne hne, qftStageFam]
  rw [if_neg (by omega)]

/-- **One whole stage of the outer loop.** Advancing the mid-stage family's own
wire by the ladder phase lands on the next stage of the invariant: the head
`xᵢ·π` plus the ladder is precisely `qftAngle x i`
(`qftAngle_eq_head_add_ladder`). -/
theorem qftStageMid_step (i : Fin n) :
    Function.update (qftStageMid n x i) i
        (phaseKet (bitVal (x i) * Real.pi
          + ∑ j : Fin (n - 1 - (i : ℕ)),
              bitVal (x (finTarget i.isLt j)) * (2 * Real.pi / 2 ^ ((j : ℕ) + 2))))
      = qftStageFam n x ((i : ℕ) + 1) := by
  funext j
  by_cases hj : j = i
  · rw [hj, Function.update_self]
    simp only [qftStageFam]
    rw [if_pos (Nat.lt_succ_self _), qftAngle_eq_head_add_ladder x i.isLt]
  · rw [Function.update_of_ne hj]
    have hjv : (j : ℕ) ≠ (i : ℕ) := fun hc => hj (Fin.ext hc)
    simp only [qftStageMid, Function.update_of_ne hj, qftStageFam]
    by_cases hlt : (j : ℕ) < (i : ℕ)
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

end StageFamily

/-! ## §9. The reversal network

The wire permutation that closes the QFT: CoqQ's `rev_ord` and the `⌊n/2⌋`
transpositions of `rev_circuit` (`example/coqq_paper/example.v:140`, `RevTuple`),
together with the invariant "the outermost `m` pairs are already swapped". Pure
index and state algebra: the swap network itself is a program and stays in the
example. -/

/-- The mirror index `n-1-i`. CoqQ `rev_ord` (mathcomp `fintype.v`). -/
def revIdx {n : ℕ} (i : Fin n) : Fin n := ⟨n - 1 - (i : ℕ), by have := i.isLt; omega⟩

theorem revIdx_val {n : ℕ} (i : Fin n) : ((revIdx i : Fin n) : ℕ) = n - 1 - (i : ℕ) := rfl

/-- The left wire of the `k`-th transposition of the reversal network. -/
def revA {n : ℕ} (k : Fin (n / 2)) : Fin n := ⟨(k : ℕ), by have := k.isLt; omega⟩

/-- The right wire of the `k`-th transposition of the reversal network. -/
def revB {n : ℕ} (k : Fin (n / 2)) : Fin n := ⟨n - 1 - (k : ℕ), by have := k.isLt; omega⟩

theorem revA_val {n : ℕ} (k : Fin (n / 2)) : ((revA k : Fin n) : ℕ) = (k : ℕ) := rfl

theorem revB_val {n : ℕ} (k : Fin (n / 2)) : ((revB k : Fin n) : ℕ) = n - 1 - (k : ℕ) := rfl

/-- A transposition of the reversal network names two distinct cells: `k < n/2`
forces `k < n-1-k`. -/
theorem revA_ne_revB {n : ℕ} (k : Fin (n / 2)) : revA k ≠ revB k := by
  have hk := k.isLt
  have hA := revA_val k
  have hB := revB_val k
  intro h
  have := congrArg Fin.val h
  omega

section RevFamily

variable {n : ℕ} (φ : Fin n → 𝕢)

/-- **The invariant of the reversal network**: after `m` transpositions the
outermost `m` pairs of wires have been swapped, the middle block is untouched. -/
noncomputable def qftRevFam (m : ℕ) (i : Fin n) : 𝕢 :=
  if (i : ℕ) < m ∨ n - 1 - m < (i : ℕ) then φ (revIdx i) else φ i

/-- The reversal invariant only permutes the given family, so it stays unit. -/
@[simp]
theorem norm_qftRevFam (hφ : ∀ i, ‖φ i‖ = 1) (m : ℕ) (i : Fin n) :
    ‖qftRevFam φ m i‖ = 1 := by
  simp only [qftRevFam]
  split
  · exact hφ _
  · exact hφ _

/-- **Start of the reversal loop**: nothing has been swapped yet. -/
theorem qftRevFam_zero : qftRevFam φ 0 = φ := by
  funext i
  have hi := i.isLt
  simp only [qftRevFam]
  rw [if_neg (by omega)]

/-- **End of the reversal loop**: after `⌊n/2⌋` transpositions every wire has
been mirrored — including, when `n` is odd, the central wire, which is its own
mirror. -/
theorem qftRevFam_half : qftRevFam φ (n / 2) = fun i => φ (revIdx i) := by
  funext i
  have hi := i.isLt
  simp only [qftRevFam]
  split_ifs with h
  · rfl
  · obtain ⟨h1, h2⟩ := not_or.mp h
    have hfix : revIdx i = i := Fin.ext (by rw [revIdx_val]; omega)
    rw [hfix]

/-- The left wire of the `k`-th transposition is still unswapped at stage `k`. -/
theorem qftRevFam_left (k : Fin (n / 2)) : qftRevFam φ (k : ℕ) (revA k) = φ (revA k) := by
  have hk := k.isLt
  have hA := revA_val k
  simp only [qftRevFam]
  rw [if_neg (by omega)]

/-- The right wire of the `k`-th transposition is still unswapped at stage `k`. -/
theorem qftRevFam_right (k : Fin (n / 2)) : qftRevFam φ (k : ℕ) (revB k) = φ (revB k) := by
  have hk := k.isLt
  have hB := revB_val k
  simp only [qftRevFam]
  rw [if_neg (by omega)]

/-- **One transposition of the reversal loop**: exchanging the contents of the
wires `revA k` and `revB k` advances the invariant by one stage. -/
theorem qftRevFam_step (k : Fin (n / 2)) :
    Function.update (Function.update (qftRevFam φ (k : ℕ)) (revA k) (φ (revB k)))
        (revB k) (φ (revA k))
      = qftRevFam φ ((k : ℕ) + 1) := by
  have hk := k.isLt
  have hA := revA_val k
  have hB := revB_val k
  funext i
  by_cases hib : i = revB k
  · rw [hib, Function.update_self]
    simp only [qftRevFam]
    rw [if_pos (by omega)]
    exact congrArg φ (Fin.ext (by rw [revIdx_val]; omega))
  · rw [Function.update_of_ne hib]
    by_cases hia : i = revA k
    · rw [hia, Function.update_self]
      simp only [qftRevFam]
      rw [if_pos (by omega)]
      exact congrArg φ (Fin.ext (by rw [revIdx_val]; omega))
    · rw [Function.update_of_ne hia]
      have hiv := i.isLt
      have h1 : (i : ℕ) ≠ (k : ℕ) := fun hc => hia (Fin.ext (by omega))
      have h2 : (i : ℕ) ≠ n - 1 - (k : ℕ) := fun hc => hib (Fin.ext (by omega))
      simp only [qftRevFam]
      by_cases hcond : (i : ℕ) < (k : ℕ) ∨ n - 1 - (k : ℕ) < (i : ℕ)
      · rw [if_pos hcond, if_pos (by omega)]
      · rw [if_neg hcond, if_neg (by omega)]

end RevFamily

/-- **The Hadamard is its own inverse on the head phases**: `H 'ph (b·π) = ∣b⟩`,
the converse move of `H_qbit` (`H ∣b⟩ = 'ph (b·π)`), by `H ∣+⟩ = ∣0⟩` and
`H ∣−⟩ = ∣1⟩`. This is the gate content of the Hadamard step of a *backward*
QFT stage — the inverse-QFT circuit undoing `H_qbit`. -/
theorem H_phaseKet_bit (b : Bool) :
    (H : 𝕢 →ₗ[ℂ] 𝕢) (phaseKet (bitVal b * Real.pi)) = qbit b := by
  cases b
  · rw [bitVal_false, zero_mul, phaseKet_zero, H_qplus, qbit_false]
  · rw [bitVal_true, one_mul, phaseKet_pi, H_qminus, qbit_true]

/-! ## §9b. The stage families read at a `ℕ`-valued loop counter

A counted `while` loop (`Qhl/Logic/CountedWhile.lean`) indexes its invariant by
an unbounded counter `k : ℕ` and pins `k < n` only through its step masks.
These are §8–§9's families re-read at such a counter through `cell`
(`Qhl/Register/Qubits.lean`), with each endpoint and update law stated under
the explicit bound the mask provides. As everywhere in this file: no program,
no triple and no proof rule occurs. -/

section CountedFamilies

variable (n : ℕ) [NeZero n] (x : Fin n → Bool)

/-- The head phase deposited by the Hadamard of stage `k`: `xₖ·π`. -/
noncomputable def qftHeadPhase (k : ℕ) : ℝ := bitVal (x (cell n k)) * Real.pi

/-- The target bits of stage `k`'s ladder, read through `cell`. -/
def qftLadBits (k : ℕ) : Fin (n - 1 - k) → Bool :=
  fun j => x (cell n (k + 1 + (j : ℕ)))

/-- The mid-stage family at counter value `k`: the Hadamard of stage `k` has
fired, its ladder has not yet run (`qftStageMid`, read at a `ℕ` counter). -/
noncomputable def qftStageMidN (k : ℕ) : Fin n → 𝕢 :=
  Function.update (qftStageFam n x k) (cell n k) (phaseKet (qftHeadPhase n x k))

/-- The ladder family of stage `k` at rung `j`: `qftLadderFam` at control cell
`cell n k` over the mid-stage family. -/
noncomputable def qftLadderFamN (k j : ℕ) : Fin n → 𝕢 :=
  qftLadderFam (cell n k) (qftLadBits n x k) (qftHeadPhase n x k)
    (qftStageMidN n x k) j

/-- The reversal family at transposition `m`, over the per-wire phase kets. -/
noncomputable def qftRevFamN (m : ℕ) : Fin n → 𝕢 :=
  qftRevFam (fun i => phaseKet (qftAngle x (i : ℕ))) m

theorem norm_qftStageMidN (k : ℕ) (i : Fin n) : ‖qftStageMidN n x k i‖ = 1 :=
  norm_update_unit_eq_one (norm_qftStageFam n x k) (norm_phaseKet _) i

theorem norm_qftLadderFamN (k j : ℕ) (i : Fin n) : ‖qftLadderFamN n x k j i‖ = 1 :=
  norm_qftLadderFam (cell n k) (qftLadBits n x k) (qftHeadPhase n x k)
    (qftStageMidN n x k) (norm_qftStageMidN n x k) j i

theorem norm_qftRevFamN (m : ℕ) (i : Fin n) : ‖qftRevFamN n x m i‖ = 1 :=
  norm_qftRevFam _ (fun _ => norm_phaseKet _) m i

/-- A counter value below the bound reads the ladder target as `finTarget`. -/
theorem cell_eq_finTarget {k : ℕ} (hk : k < n) (j : Fin (n - 1 - k)) :
    cell n (k + 1 + (j : ℕ)) = finTarget hk j :=
  Fin.ext (by rw [cell_val n (by have := j.isLt; omega), finTarget_val])

/-- The stage family still carries the input bit on its own wire. -/
theorem qftStageFam_cell {k : ℕ} (hk : k < n) :
    qftStageFam n x k (cell n k) = qbit (x (cell n k)) := by
  simp only [qftStageFam]
  rw [cell_val n hk, if_neg (lt_irrefl k)]

/-- The mid-stage family agrees with the `Fin`-indexed `qftStageMid` on the
loop masks. -/
theorem qftStageMidN_eq {k : ℕ} (hk : k < n) :
    qftStageMidN n x k = qftStageMid n x ⟨k, hk⟩ := by
  rw [qftStageMidN, qftHeadPhase, cell_eq_mk n hk, qftStageMid]

/-- **The Hadamard step of a stage**: updating the stage wire by `H` of its
input bit lands on the mid-stage family — the `ℕ`-counter form of
`qftStageMid_eq_update_H`. -/
theorem qftStageMidN_eq_update_H {k : ℕ} (hk : k < n) :
    Function.update (qftStageFam n x k) (cell n k)
        ((H : 𝕢 →ₗ[ℂ] 𝕢) (qftStageFam n x k (cell n k)))
      = qftStageMidN n x k := by
  rw [qftStageFam_cell n x hk, H_qbit, qftStageMidN, qftHeadPhase]

/-- The rung target still carries its input bit. -/
theorem qftStageMidN_tgt {k j : ℕ} (hk : k < n) (hj : j < n - 1 - k) :
    qftStageMidN n x k (cell n (k + 1 + j)) = qbit (x (cell n (k + 1 + j))) := by
  have hlt : k + 1 + j < n := by omega
  have hne : cell n (k + 1 + j) ≠ cell n k := cell_ne n hlt hk (by omega)
  rw [qftStageMidN, Function.update_of_ne hne]
  simp only [qftStageFam]
  rw [cell_val n hlt, if_neg (by omega)]

/-- Ladder entry: at rung `0` the ladder family is the mid-stage family
(library `qftLadderFam_zero`); no bound on `k` is needed. -/
theorem qftLadderFamN_zero (k : ℕ) : qftLadderFamN n x k 0 = qftStageMidN n x k :=
  qftLadderFam_zero (cell n k) (qftLadBits n x k) (qftHeadPhase n x k)
    (qftStageMidN n x k) (by rw [qftStageMidN]; exact Function.update_self _ _ _)

/-- The control value at rung `j`: the head phase plus the ladder sum. -/
theorem qftLadderFamN_ctrl (k j : ℕ) :
    qftLadderFamN n x k j (cell n k)
      = phaseKet (qftHeadPhase n x k + qftLadderSum (qftLadBits n x k) j) :=
  qftLadderFam_ctrl (cell n k) (qftLadBits n x k) (qftHeadPhase n x k)
    (qftStageMidN n x k) j

/-- The target value at rung `j`: still the input bit. -/
theorem qftLadderFamN_tgt {k j : ℕ} (hk : k < n) (hj : j < n - 1 - k) :
    qftLadderFamN n x k j (cell n (k + 1 + j)) = qbit (x (cell n (k + 1 + j))) := by
  have hne : cell n k ≠ cell n (k + 1 + j) := cell_ne n hk (by omega) (by omega)
  rw [qftLadderFamN, qftLadderFam_of_ne (cell n k) (qftLadBits n x k)
    (qftHeadPhase n x k) (qftStageMidN n x k) (Ne.symm hne) j]
  exact qftStageMidN_tgt n x hk hj

/-- One rung's family update (library `qftLadderFam_step`). -/
theorem qftLadderFamN_step {k j : ℕ} (hk : k < n) (hj : j < n - 1 - k) :
    Function.update
        (Function.update (qftLadderFamN n x k j) (cell n k)
          (phaseKet (qftHeadPhase n x k + qftLadderSum (qftLadBits n x k) j
            + bitVal (x (cell n (k + 1 + j))) * (2 * Real.pi / 2 ^ (j + 2)))))
        (cell n (k + 1 + j)) (qbit (x (cell n (k + 1 + j))))
      = qftLadderFamN n x k (j + 1) :=
  qftLadderFam_step (cell n k) (qftLadBits n x k) (qftHeadPhase n x k)
    (qftStageMidN n x k) (⟨j, hj⟩ : Fin (n - 1 - k))
    (cell_ne n hk (by omega) (by omega)) (qftStageMidN_tgt n x hk hj)

/-- Ladder exit: the full ladder lands on the next stage family
(`qftLadderFam_full` + `qftStageMid_step`). -/
theorem qftLadderFamN_full {k : ℕ} (hk : k < n) :
    qftLadderFamN n x k (n - 1 - k) = qftStageFam n x (k + 1) := by
  rw [qftLadderFamN, qftLadderFam_full, qftStageMidN_eq n x hk, qftHeadPhase,
    cell_eq_mk n hk]
  simp only [qftLadBits, cell_eq_finTarget n hk]
  exact qftStageMid_step n x ⟨k, hk⟩

/-- The left wire of transposition `k` is still unswapped. -/
theorem qftRevFamN_left {k : ℕ} (hk : k < n / 2) :
    qftRevFamN n x k (cell n k) = phaseKet (qftAngle x k) := by
  have hA : cell n k = revA (⟨k, hk⟩ : Fin (n / 2)) :=
    Fin.ext (cell_val n (by omega))
  rw [qftRevFamN, hA]
  exact qftRevFam_left _ ⟨k, hk⟩

/-- The right wire of transposition `k` is still unswapped. -/
theorem qftRevFamN_right {k : ℕ} (hk : k < n / 2) :
    qftRevFamN n x k (cell n (n - 1 - k)) = phaseKet (qftAngle x (n - 1 - k)) := by
  have hB : cell n (n - 1 - k) = revB (⟨k, hk⟩ : Fin (n / 2)) :=
    Fin.ext (cell_val n (by omega))
  rw [qftRevFamN, hB]
  exact qftRevFam_right _ ⟨k, hk⟩

/-- One transposition's family update (library `qftRevFam_step`). -/
theorem qftRevFamN_step {k : ℕ} (hk : k < n / 2) :
    Function.update
        (Function.update (qftRevFamN n x k) (cell n k)
          (phaseKet (qftAngle x (n - 1 - k))))
        (cell n (n - 1 - k)) (phaseKet (qftAngle x k))
      = qftRevFamN n x (k + 1) := by
  have hA : cell n k = revA (⟨k, hk⟩ : Fin (n / 2)) :=
    Fin.ext (cell_val n (by omega))
  have hB : cell n (n - 1 - k) = revB (⟨k, hk⟩ : Fin (n / 2)) :=
    Fin.ext (cell_val n (by omega))
  rw [hA, hB]
  exact qftRevFam_step _ ⟨k, hk⟩

/-! ### §9c. The backward run of the stage families

The inverse-QFT **circuit** (`Qhl/Examples/InverseQFTTriple.lean`, the reversed
gate sequence of the QFT circuit with inverted phases) traverses the very same
families in the opposite direction: its ladder loops read `qftLadderFamN` at a
*decreasing* rung index, its Hadamard steps undo `qftStageMidN`, and its
reversal loop runs `qftRevFam` from the Fourier side back to the stage-complete
side. These are the endpoint/update laws of that backward traversal — as
everywhere in this file: no program, no triple and no proof rule occurs. -/

/-- The ladder target carries its input bit at **every** rung index of the
family — `qftLadderFamN_tgt` decoupled from the family index, which is what a
ladder read at a decreasing index consumes. -/
theorem qftLadderFamN_tgt_any (m : ℕ) {k j : ℕ} (hk : k < n) (hj : j < n - 1 - k) :
    qftLadderFamN n x k m (cell n (k + 1 + j)) = qbit (x (cell n (k + 1 + j))) := by
  have hne : cell n k ≠ cell n (k + 1 + j) := cell_ne n hk (by omega) (by omega)
  rw [qftLadderFamN, qftLadderFam_of_ne (cell n k) (qftLadBits n x k)
    (qftHeadPhase n x k) (qftStageMidN n x k) (Ne.symm hne) m]
  exact qftStageMidN_tgt n x hk hj

/-- **One rung of the ladder loop, run backwards**: withdrawing the `j`-th
rung's phase from the control and rewriting the target back to its (unchanged)
basis ket lands exactly on the *previous* stage of the invariant — the converse
of `qftLadderFamN_step`, consumed by the inverse-QFT ladder (whose gate content
is `cphase_vpair_phaseKet` at the inverted angle `−2π/2^(j+2)`). -/
theorem qftLadderFamN_step_rev {k j : ℕ} (hk : k < n) (hj : j < n - 1 - k) :
    Function.update
        (Function.update (qftLadderFamN n x k (j + 1)) (cell n k)
          (phaseKet (qftHeadPhase n x k + qftLadderSum (qftLadBits n x k) j)))
        (cell n (k + 1 + j)) (qbit (x (cell n (k + 1 + j))))
      = qftLadderFamN n x k j := by
  funext i
  by_cases hit : i = cell n (k + 1 + j)
  · rw [hit, Function.update_self]
    exact (qftLadderFamN_tgt_any n x j hk hj).symm
  · rw [Function.update_of_ne hit]
    by_cases hic : i = cell n k
    · rw [hic, Function.update_self]
      exact (qftLadderFamN_ctrl n x k j).symm
    · rw [Function.update_of_ne hic, qftLadderFamN, qftLadderFam_of_ne (cell n k)
        (qftLadBits n x k) (qftHeadPhase n x k) (qftStageMidN n x k) hic (j + 1),
        qftLadderFamN, qftLadderFam_of_ne (cell n k) (qftLadBits n x k)
        (qftHeadPhase n x k) (qftStageMidN n x k) hic j]

/-- **The Hadamard step of a stage, run backwards**: applying `H` to the stage
wire of the *mid-stage* family recovers the stage family — the converse of
`qftStageMidN_eq_update_H`, by `H_phaseKet_bit` (`H` is its own inverse on the
head phases). -/
theorem qftStageMidN_step_H {k : ℕ} (hk : k < n) :
    Function.update (qftStageMidN n x k) (cell n k)
        ((H : 𝕢 →ₗ[ℂ] 𝕢) (qftStageMidN n x k (cell n k)))
      = qftStageFam n x k := by
  have hself : qftStageMidN n x k (cell n k) = phaseKet (qftHeadPhase n x k) := by
    rw [qftStageMidN]
    exact Function.update_self _ _ _
  rw [hself, qftHeadPhase, H_phaseKet_bit, qftStageMidN, Function.update_idem,
    ← qftStageFam_cell n x hk]
  exact Function.update_eq_self _ _

/-- **One controlled-phase rung of a QFT stage, as a whole-world action**: the
gate `cR(2π/2^(j+2))` at the pair `(cell k, cell (k+1+j))`, lifted to the whole
world (`regLift_pairGate_prodV`, the frame carried through), advances the
ladder family one rung — the gate content is `cphase_vpair_phaseKet` on the
family values `qftLadderFamN_ctrl`/`qftLadderFamN_tgt`, the family update is
`qftLadderFamN_step`. The one rung-level verification condition of the QFT's
ladder loop, packaged once for the derivation rung and the composite-operator
reading alike. -/
theorem regLift_cphase_qftLadderFamN {k j : ℕ} (hk : k < n) (hj : j < n - 1 - k)
    (hne : cell n k ≠ cell n (k + 1 + j)) :
    regLift (D := QubitD n) (Reg.pair (cell n k) (cell n (k + 1 + j)) hne)
        (pairGate (D := QubitD n) (cell n k) (cell n (k + 1 + j)) hne
          (cphase (2 * Real.pi / 2 ^ (j + 2))))
        (prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftLadderFamN n x k j))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (qftLadderFamN n x k (j + 1)) := by
  have hG : (cphase (2 * Real.pi / 2 ^ (j + 2)) :
        EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair (qftLadderFamN n x k j (cell n k))
          (qftLadderFamN n x k j (cell n (k + 1 + j))))
      = vpair (phaseKet (qftHeadPhase n x k + qftLadderSum (qftLadBits n x k) j
            + bitVal (x (cell n (k + 1 + j))) * (2 * Real.pi / 2 ^ (j + 2))))
          (qbit (x (cell n (k + 1 + j)))) := by
    rw [qftLadderFamN_ctrl, qftLadderFamN_tgt n x hk hj, cphase_vpair_phaseKet]
  rw [regLift_pairGate_prodV (cell n k) (cell n (k + 1 + j)) hne
    (cphase (2 * Real.pi / 2 ^ (j + 2))) (qftLadderFamN n x k j) hG]
  exact congrArg _ (qftLadderFamN_step n x hk hj)

/-- **One controlled-phase rung of the ladder loop, run backwards**, as a
whole-world action, in the reversed-run coordinates (reversed stage counter
`k'`, reversed rung counter `j'`): the inverted gate `cR(−2π/2^((k'−1−j')+2))`
at the reversed pair `(cell (n−1−k'), cell (n−1−j'))` walks the ladder family
of original stage `n−1−k'` one step down — the gate content is
`cphase_vpair_phaseKet` at the inverted angle with `qftLadderSum_succ`
withdrawing the rung's phase, the family update is `qftLadderFamN_step_rev`.
The mirror of `regLift_cphase_qftLadderFamN`, packaged once for the
inverse-QFT circuit's derivation rung and composite-operator reading alike. -/
theorem regLift_cphase_neg_qftLadderFamN {k' j' : ℕ} (hk : k' < n) (hj : j' < k')
    (hne : cell n (n - 1 - k') ≠ cell n (n - 1 - j')) :
    regLift (D := QubitD n) (Reg.pair (cell n (n - 1 - k')) (cell n (n - 1 - j')) hne)
        (pairGate (D := QubitD n) (cell n (n - 1 - k')) (cell n (n - 1 - j')) hne
          (cphase (-(2 * Real.pi / 2 ^ (k' - 1 - j' + 2)))))
        (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (qftLadderFamN n x (n - 1 - k') (k' - j')))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (qftLadderFamN n x (n - 1 - k') (k' - (j' + 1))) := by
  have hkn : n - 1 - k' < n := by omega
  have hjk : k' - 1 - j' < n - 1 - (n - 1 - k') := by omega
  have ht : cell n (n - 1 - j') = cell n ((n - 1 - k') + 1 + (k' - 1 - j')) := by
    congr 1
    omega
  have hidx1 : k' - j' = (k' - 1 - j') + 1 := by omega
  have hsum : qftLadderSum (qftLadBits n x (n - 1 - k')) (k' - j')
      = qftLadderSum (qftLadBits n x (n - 1 - k')) (k' - 1 - j')
        + bitVal (x (cell n ((n - 1 - k') + 1 + (k' - 1 - j'))))
          * (2 * Real.pi / 2 ^ ((k' - 1 - j') + 2)) := by
    rw [hidx1]
    exact qftLadderSum_succ (qftLadBits n x (n - 1 - k')) hjk
  have hG : (cphase (-(2 * Real.pi / 2 ^ (k' - 1 - j' + 2))) :
        EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair (qftLadderFamN n x (n - 1 - k') (k' - j') (cell n (n - 1 - k')))
          (qftLadderFamN n x (n - 1 - k') (k' - j') (cell n (n - 1 - j'))))
      = vpair (phaseKet (qftHeadPhase n x (n - 1 - k')
            + qftLadderSum (qftLadBits n x (n - 1 - k')) (k' - 1 - j')))
          (qbit (x (cell n ((n - 1 - k') + 1 + (k' - 1 - j'))))) := by
    rw [ht, qftLadderFamN_ctrl, qftLadderFamN_tgt_any n x (k' - j') hkn hjk,
      cphase_vpair_phaseKet]
    exact congrArg (fun s => vpair (phaseKet s)
      (qbit (x (cell n ((n - 1 - k') + 1 + (k' - 1 - j')))))) (by rw [hsum]; ring)
  rw [regLift_pairGate_prodV (cell n (n - 1 - k')) (cell n (n - 1 - j')) hne
    (cphase (-(2 * Real.pi / 2 ^ (k' - 1 - j' + 2))))
    (qftLadderFamN n x (n - 1 - k') (k' - j')) hG]
  rw [ht, hidx1, show k' - (j' + 1) = k' - 1 - j' from by omega]
  exact congrArg _ (qftLadderFamN_step_rev n x hkn hjk)

/-- The left wire of transposition `k` of the reversal network, at an arbitrary
per-wire family — `qftRevFam_left` read through `cell`. -/
theorem qftRevFam_left_cell (φv : Fin n → 𝕢) {k : ℕ} (hk : k < n / 2) :
    qftRevFam φv k (cell n k) = φv (cell n k) := by
  have hA : cell n k = revA (⟨k, hk⟩ : Fin (n / 2)) := Fin.ext (cell_val n (by omega))
  rw [hA]
  exact qftRevFam_left _ ⟨k, hk⟩

/-- The right wire of transposition `k` of the reversal network, at an
arbitrary per-wire family — `qftRevFam_right` read through `cell`. -/
theorem qftRevFam_right_cell (φv : Fin n → 𝕢) {k : ℕ} (hk : k < n / 2) :
    qftRevFam φv k (cell n (n - 1 - k)) = φv (cell n (n - 1 - k)) := by
  have hB : cell n (n - 1 - k) = revB (⟨k, hk⟩ : Fin (n / 2)) :=
    Fin.ext (cell_val n (by omega))
  rw [hB]
  exact qftRevFam_right _ ⟨k, hk⟩

/-- One transposition of the reversal network, at an arbitrary per-wire family
— `qftRevFam_step` read through `cell`. Generic in the family, so it serves
both the forward run (`qftRevFamN`, the QFT closing its stage loop) and the
backward run (`iqftRevFamN`, the inverse-QFT circuit opening). -/
theorem qftRevFam_step_cell (φv : Fin n → 𝕢) {k : ℕ} (hk : k < n / 2) :
    Function.update
        (Function.update (qftRevFam φv k) (cell n k) (φv (cell n (n - 1 - k))))
        (cell n (n - 1 - k)) (φv (cell n k))
      = qftRevFam φv (k + 1) := by
  have hA : cell n k = revA (⟨k, hk⟩ : Fin (n / 2)) := Fin.ext (cell_val n (by omega))
  have hB : cell n (n - 1 - k) = revB (⟨k, hk⟩ : Fin (n / 2)) :=
    Fin.ext (cell_val n (by omega))
  rw [hA, hB]
  exact qftRevFam_step _ ⟨k, hk⟩

/-- **The invariant of the reversal network run from the Fourier side**: the
reversal family over the *mirrored* phase kets — at `m = 0` the wire profile of
the Fourier state (`fourierState_eq_prodV`), at `m = ⌊n/2⌋` the stage-complete
profile `'ph (qftAngle x i)` (`qftStageFam_full`). The invariant of the swap
loop that *opens* the inverse-QFT circuit. -/
noncomputable def iqftRevFamN (m : ℕ) : Fin n → 𝕢 :=
  qftRevFam (fun j => phaseKet (qftAngle x (n - 1 - (j : ℕ)))) m

theorem norm_iqftRevFamN (m : ℕ) (i : Fin n) : ‖iqftRevFamN n x m i‖ = 1 :=
  norm_qftRevFam _ (fun _ => norm_phaseKet _) m i

/-- **Start of the backward reversal loop**: the mirrored profile — exactly the
product form of the Fourier state (`fourierState_eq_prodV`). -/
theorem iqftRevFamN_zero :
    iqftRevFamN n x 0 = fun j : Fin n => phaseKet (qftAngle x (n - 1 - (j : ℕ))) :=
  qftRevFam_zero _

/-- **End of the backward reversal loop**: every wire carries its own Fourier
phase — the stage-complete profile `qftStageFam_full`. -/
theorem iqftRevFamN_half :
    iqftRevFamN n x (n / 2) = fun i : Fin n => phaseKet (qftAngle x (i : ℕ)) := by
  rw [iqftRevFamN, qftRevFam_half]
  funext i
  have hi := i.isLt
  have hv : n - 1 - ((revIdx i : Fin n) : ℕ) = (i : ℕ) := by
    rw [revIdx_val]
    omega
  rw [hv]

/-- The left wire of transposition `k` is still mirrored at stage `k` of the
backward run. -/
theorem iqftRevFamN_left {k : ℕ} (hk : k < n / 2) :
    iqftRevFamN n x k (cell n k) = phaseKet (qftAngle x (n - 1 - k)) := by
  rw [iqftRevFamN, qftRevFam_left_cell n _ hk, cell_val n (by omega)]

/-- The right wire of transposition `k` is still mirrored at stage `k` of the
backward run. -/
theorem iqftRevFamN_right {k : ℕ} (hk : k < n / 2) :
    iqftRevFamN n x k (cell n (n - 1 - k)) = phaseKet (qftAngle x k) := by
  rw [iqftRevFamN, qftRevFam_right_cell n _ hk, cell_val n (by omega)]
  have hv : n - 1 - (n - 1 - k) = k := by omega
  rw [hv]

/-- **One transposition of the backward reversal loop**: exchanging the
contents of the wires `k` and `n−1−k` restores both to their own Fourier
phase. -/
theorem iqftRevFamN_step {k : ℕ} (hk : k < n / 2) :
    Function.update
        (Function.update (iqftRevFamN n x k) (cell n k) (phaseKet (qftAngle x k)))
        (cell n (n - 1 - k)) (phaseKet (qftAngle x (n - 1 - k)))
      = iqftRevFamN n x (k + 1) := by
  have h1 : phaseKet (qftAngle x k)
      = phaseKet (qftAngle x (n - 1 - ((cell n (n - 1 - k) : Fin n) : ℕ))) := by
    rw [cell_val n (by omega)]
    have hv : n - 1 - (n - 1 - k) = k := by omega
    rw [hv]
  have h2 : phaseKet (qftAngle x (n - 1 - k))
      = phaseKet (qftAngle x (n - 1 - ((cell n k : Fin n) : ℕ))) := by
    rw [cell_val n (by omega)]
  rw [h1, h2]
  simp only [iqftRevFamN]
  exact qftRevFam_step_cell n _ hk

end CountedFamilies

/-! ## §10. The QFT operator

The quantum Fourier transform itself, as a bundled unitary of the standard
`n`-qubit world, together with its inverse. CoqQ builds it in `qtype.v` from the
fact that the Fourier profiles form an **orthonormal basis** (`QFTbv_onb`,
`qtype.v:969`): `QFT` is the unitary whose columns are those profiles, `IQFT n
:= (QFT n)^A` (`qtype.v:674`) is its adjoint, and `IQFTEt` reads off
`IQFT (QFTv i) = ''i`. We follow exactly that route.

* `natValEquiv` — the computational basis of the `n`-qubit world **is**
  `Fin (2^n)`, enumerated by `natVal`; hence `natVal_lt` and
  `natVal_injective` (CoqQ `bseq2ord`, `n2bseqK`).
* `inner_fourierState` — **the crux**, CoqQ `QFTbv_onb`. Over the computational
  basis the inner product `⟪QFTbv x, QFTbv y⟫` is the geometric sum
  `2^{-n}·∑_{v<2^n} ω^v` in the `2^n`-th root of unity
  `ω = e^{2πi(natVal y − natVal x)/2^n}`: it is `1` when `x = y` and `0`
  otherwise.
* `qftOp` — the QFT as a `UnitaryOp`, its columns the Fourier profiles, with
  `qftOp_deltav : QFT ∣x⟩ = QFTbv x`.
* `iqftOp := star (qftOp n)` and `iqftOp_fourierState` — CoqQ `IQFT` / `IQFTEt`.

Nothing here mentions a program either: this is the operator layer the
inverse-QFT and phase-estimation examples call.
-/

section QFTOperator

open scoped ComplexInnerProductSpace Matrix

/-- The mirror index is an involution. CoqQ `rev_ordK` (mathcomp `fintype.v`). -/
theorem revIdx_revIdx {n : ℕ} (i : Fin n) : revIdx (revIdx i) = i := by
  have hi := i.isLt
  refine Fin.ext ?_
  simp only [revIdx_val]
  omega

/-- The wire-mirroring permutation `i ↦ n-1-i` of an `n`-qubit world, CoqQ
`rev_ord` packaged as the involutive bijection it is. -/
def revEquiv (n : ℕ) : Fin n ≃ Fin n where
  toFun := revIdx
  invFun := revIdx
  left_inv := revIdx_revIdx
  right_inv := revIdx_revIdx

@[simp]
theorem revEquiv_apply {n : ℕ} (i : Fin n) : revEquiv n i = revIdx i := rfl

private theorem val_finTwoEquiv_symm (b : Bool) :
    ((finTwoEquiv.symm b : Fin 2) : ℕ) = if b then 1 else 0 := by
  cases b <;> rfl

/-- **The computational basis of the `n`-qubit world is `Fin (2^n)`**, enumerated
by the big-endian value `natVal`: reverse the wires (`revEquiv`, because `natVal`
is big-endian while mathlib's `finFunctionFinEquiv` is little-endian) and read
the resulting bit string as a numeral. CoqQ `bseq2ord` (`qtype.v`). -/
def natValEquiv (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (revEquiv n) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- `natValEquiv` really is `natVal`. -/
theorem natValEquiv_val {n : ℕ} (x : Fin n → Bool) :
    ((natValEquiv n x : Fin (2 ^ n)) : ℕ) = natVal x := by
  change ((finFunctionFinEquiv (fun i => finTwoEquiv.symm (x (revIdx i))) : Fin (2 ^ n)) : ℕ)
      = natVal x
  rw [finFunctionFinEquiv_apply, natVal]
  refine (Fintype.sum_equiv (revEquiv n) _ _ ?_).symm
  intro i
  rw [revEquiv_apply, revIdx_revIdx, val_finTwoEquiv_symm, revIdx_val]

/-- A big-endian `n`-bit vector has value below `2^n`. -/
theorem natVal_lt {n : ℕ} (x : Fin n → Bool) : natVal x < 2 ^ n := by
  rw [← natValEquiv_val x]
  exact (natValEquiv n x).isLt

/-- Distinct bit vectors have distinct values. CoqQ `bseq2nat_inj`. -/
theorem natVal_injective (n : ℕ) : Function.Injective (natVal (n := n)) := by
  intro x y h
  refine (natValEquiv n).injective (Fin.ext ?_)
  rw [natValEquiv_val, natValEquiv_val, h]

/-- The classical states of the full `n`-qubit world are exactly the bit
vectors: the label set is all of `Fin n`. -/
def bitsEquiv (n : ℕ) : QIdx (QubitD n) (univ : Finset (QubitL n)) ≃ (Fin n → Bool) where
  toFun l := fun i : QubitL n => l ⟨i, Finset.mem_univ i⟩
  invFun x := fun j => x (j : QubitL n)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Summing a power of a fixed scalar over the computational basis is summing it
over `Fin (2^n)`, i.e. over `range (2^n)`: the two are matched by `natVal`. -/
private theorem sum_pow_natVal (n : ℕ) (ω : ℂ) :
    ∑ l : QIdx (QubitD n) (univ : Finset (QubitL n)),
        ω ^ (natVal fun i : QubitL n => l ⟨i, Finset.mem_univ i⟩)
      = ∑ v ∈ Finset.range (2 ^ n), ω ^ v := by
  have h1 : ∑ l : QIdx (QubitD n) (univ : Finset (QubitL n)),
        ω ^ (natVal fun i : QubitL n => l ⟨i, Finset.mem_univ i⟩)
      = ∑ z : Fin n → Bool, ω ^ (natVal z) :=
    Fintype.sum_equiv (bitsEquiv n) _ _ fun _ => rfl
  have h2 : ∑ z : Fin n → Bool, ω ^ (natVal z) = ∑ v : Fin (2 ^ n), ω ^ (v : ℕ) :=
    Fintype.sum_equiv (natValEquiv n) _ _ fun z => by rw [natValEquiv_val]
  rw [h1, h2, Fin.sum_univ_eq_sum_range]

/-- **The geometric sum over a nontrivial `2^n`-th root of unity vanishes.** For
`0 < |d| < 2^n` the number `ω = e^{2πi d/2^n}` satisfies `ω^(2^n) = 1` but
`ω ≠ 1`, so `∑_{v<2^n} ω^v = (ω^(2^n)−1)/(ω−1) = 0`. This is the whole
off-diagonal content of `QFTbv_onb`. -/
private theorem geom_sum_root_eq_zero (n : ℕ) (d : ℤ) (hd : d ≠ 0) (hlt : |d| < (2 : ℤ) ^ n) :
    ∑ v ∈ Finset.range (2 ^ n),
        (Complex.exp (((2 * Real.pi * (d : ℝ) / 2 ^ n : ℝ) : ℂ) * Complex.I)) ^ v = 0 := by
  have h2C : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hpiC : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : (Complex.exp (((2 * Real.pi * (d : ℝ) / 2 ^ n : ℝ) : ℂ) * Complex.I)) ^ (2 ^ n)
      = 1 := by
    rw [← Complex.exp_nat_mul]
    have key : ((2 ^ n : ℕ) : ℂ)
          * (((2 * Real.pi * (d : ℝ) / 2 ^ n : ℝ) : ℂ) * Complex.I)
        = (d : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      field_simp
    rw [key, Complex.exp_int_mul_two_pi_mul_I]
  have hne : Complex.exp (((2 * Real.pi * (d : ℝ) / 2 ^ n : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨k, hk⟩ := h
    have hcancel : ((2 * Real.pi * (d : ℝ) / 2 ^ n : ℝ) : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ)) := by
      refine mul_right_cancel₀ Complex.I_ne_zero ?_
      rw [hk]
      ring
    push_cast at hcancel
    rw [div_eq_iff h2C] at hcancel
    have hdk : d = k * 2 ^ n := by
      have hcx : (d : ℂ) = (k : ℂ) * 2 ^ n := by
        refine mul_left_cancel₀ (mul_ne_zero (two_ne_zero) hpiC) ?_
        linear_combination hcancel
      exact_mod_cast hcx
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hd (by simpa using hdk)
    have hge : (2 : ℤ) ^ n ≤ |d| := by
      rw [hdk, abs_mul, abs_pow, abs_two]
      have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      have h2 : (0 : ℤ) < 2 ^ n := by positivity
      nlinarith
    linarith
  rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- One coordinate of the inner product of two Fourier profiles: the modulus
factors collapse to `2^{-n}` and the two phases combine into a power of the root
of unity `ω = e^{2πi(natVal y − natVal x)/2^n}`. -/
private theorem fourier_inner_term (n : ℕ) (x y : Fin n → Bool)
    (l : QIdx (QubitD n) (univ : Finset (QubitL n))) :
    star (fourierState n x l) * fourierState n y l
      = ((2 : ℂ) ^ n)⁻¹
        * (Complex.exp
            (((2 * Real.pi * (((natVal y : ℤ) - (natVal x : ℤ) : ℤ) : ℝ) / 2 ^ n : ℝ) : ℂ)
              * Complex.I)) ^ (natVal fun i : QubitL n => l ⟨i, Finset.mem_univ i⟩) := by
  have hsq : ((Real.sqrt 2 : ℂ))⁻¹ ^ n * ((Real.sqrt 2 : ℂ))⁻¹ ^ n = ((2 : ℂ) ^ n)⁻¹ := by
    rw [← mul_pow, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), inv_pow]
    norm_num
  rw [fourierState_apply, fourierState_apply, ← Complex.exp_nat_mul, Complex.star_def,
    map_mul, map_pow, map_inv₀, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, mul_mul_mul_comm, hsq, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- **The Fourier profiles are orthonormal** — CoqQ `QFTbv_onb`
(`qtype.v:969`), the fact that makes the QFT a unitary. -/
theorem inner_fourierState (n : ℕ) (x y : Fin n → Bool) :
    ⟪fourierState n x, fourierState n y⟫ = if x = y then 1 else 0 := by
  classical
  rw [dot_cdv (QubitD n)]
  simp only [cdv_apply]
  rw [Finset.sum_congr rfl fun l _ => fourier_inner_term n x y l, ← Finset.mul_sum,
    sum_pow_natVal]
  by_cases hxy : x = y
  · subst hxy
    have hω : Complex.exp
        (((2 * Real.pi * (((natVal x : ℤ) - (natVal x : ℤ) : ℤ) : ℝ) / 2 ^ n : ℝ) : ℂ)
          * Complex.I) = 1 := by
      rw [sub_self]
      norm_num
    rw [hω, if_pos rfl]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [show ((2 ^ n : ℕ) : ℂ) = (2 : ℂ) ^ n by push_cast; ring,
      inv_mul_cancel₀ (pow_ne_zero _ (two_ne_zero))]
  · rw [if_neg hxy]
    have hd : ((natVal y : ℤ) - (natVal x : ℤ)) ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro h
      exact hxy (natVal_injective n (by exact_mod_cast h.symm))
    have hx := natVal_lt x
    have hy := natVal_lt y
    have hx' : ((natVal x : ℤ)) < 2 ^ n := by exact_mod_cast hx
    have hy' : ((natVal y : ℤ)) < 2 ^ n := by exact_mod_cast hy
    have hx0 : (0 : ℤ) ≤ (natVal x : ℤ) := Int.natCast_nonneg _
    have hy0 : (0 : ℤ) ≤ (natVal y : ℤ) := Int.natCast_nonneg _
    have hlt : |((natVal y : ℤ) - (natVal x : ℤ))| < (2 : ℤ) ^ n := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    rw [geom_sum_root_eq_zero n _ hd hlt, mul_zero]

/-! ### The unitary -/

/-- **The matrix of the quantum Fourier transform**: its `m`-th column is the
Fourier profile of the bit vector `m`. CoqQ `QFT` (`qtype.v`). -/
noncomputable def qftMat (n : ℕ) :
    Matrix (QIdx (QubitD n) (univ : Finset (QubitL n)))
      (QIdx (QubitD n) (univ : Finset (QubitL n))) ℂ :=
  fun l m => fourierState n (fun i : QubitL n => m ⟨i, Finset.mem_univ i⟩) l

/-- **The quantum Fourier transform** of the standard `n`-qubit world, a genuine
unitary: its columns are the orthonormal family `inner_fourierState`. CoqQ
`QFT` (`qtype.v`). -/
noncomputable def qftOp (n : ℕ) : UnitaryOp (HS (QubitD n) (univ : Finset (QubitL n))) :=
  unitaryOfMat (qftMat n) <| by
    ext m₁ m₂
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hcol : ∀ a : QIdx (QubitD n) (univ : Finset (QubitL n)),
        ∑ l, (qftMat n)ᴴ a l * qftMat n l m₂
          = ⟪fourierState n (fun i : QubitL n => a ⟨i, Finset.mem_univ i⟩),
              fourierState n (fun i : QubitL n => m₂ ⟨i, Finset.mem_univ i⟩)⟫ := by
      intro a
      rw [dot_cdv (QubitD n)]
      exact Finset.sum_congr rfl fun l _ => by
        rw [Matrix.conjTranspose_apply]
        rfl
    rw [hcol, inner_fourierState]
    refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
    · funext j
      have := congrFun h (j : QubitL n)
      exact this
    · rw [h]

@[simp]
theorem coe_qftOp (n : ℕ) :
    (qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n)))
      = matOp (qftMat n) := rfl

/-- **The defining action of the QFT**: it sends the computational basis ket
`∣x⟩` to the Fourier profile of `x`. CoqQ `QFTv`/`QFTEt` (`qtype.v`). -/
theorem qftOp_deltav (n : ℕ) (x : Fin n → Bool) :
    (qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n)))
        (deltav (QubitD n) (fun i => x (i : QubitL n)))
      = fourierState n x := by
  refine PiLp.ext fun l => ?_
  rw [coe_qftOp, matOp_apply]
  rw [Finset.sum_eq_single (fun i : ↥(univ : Finset (QubitL n)) => x (i : QubitL n))]
  · rw [deltav_apply, if_pos rfl, mul_one]
    rfl
  · intro m _ hm
    rw [deltav_apply, if_neg hm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### The inverse -/

/-- **The inverse quantum Fourier transform**, the adjoint of the QFT. CoqQ
`IQFT n := (QFT n)^A` (`qtype.v:674`). -/
noncomputable def iqftOp (n : ℕ) : UnitaryOp (HS (QubitD n) (univ : Finset (QubitL n))) :=
  star (qftOp n)

theorem coe_iqftOp (n : ℕ) :
    (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n)))
      = LinearMap.adjoint (qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) :=
  LinearMap.star_eq_adjoint _

/-- **The action lemma of the inverse QFT** — CoqQ `IQFTEt`: the IQFT sends the
Fourier profile of `x` back to the computational basis ket `∣x⟩`. It is the
unitarity of `qftOp` read at `qftOp_deltav`. -/
theorem iqftOp_fourierState (n : ℕ) (x : Fin n → Bool) :
    (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n))) (fourierState n x)
      = deltav (QubitD n) (fun i => x (i : QubitL n)) := by
  rw [coe_iqftOp, ← qftOp_deltav n x]
  exact adjoint_apply_apply (qftOp n).isUnitary _

end QFTOperator

/-! ## §11. The QPE stage algebra (exact case)

The state algebra of the standard multi-qubit binary **phase estimation** on the
`(n+1)`-qubit world: the `n` cells `Fin.castSucc k` form the counting register,
the last cell `Fin.last n` carries an eigenstate `ψ` of the unitary whose phase
is being read. Everything here is the **exact** case `θ = natVal x / 2^n` of
CoqQ's `PhaseEstimation` (`example/coqq_paper/example.v:980-1035`,
`RS_QPE`/`RS_QPE_exact`, under the eigenvalue hypothesis `eigU`): the phase is a
dyadic rational of denominator `2^n`, so every controlled power lands exactly on
a QFT angle and the inverse QFT reads off the bit vector `x`.

* `phaseKet_add_int_mul_two_pi`, `two_pi_natVal_pow`, `phaseKet_kick` — the
  phase arithmetic of the kickback: the angle `2^i·2πθ` that the `i`-th
  controlled power deposits on its control wire *is* the QFT angle
  `qftAngle x i`, up to the whole turns contributed by the bits above position
  `i` — turns a phase ket does not see. This is the QPE counterpart of
  `qftAngle_sum_eq` (§4), proved the same way, one bit position at a time.
* `qpeInitFam`, `qpePlusFam`, `qpeKickFam`, `qpePhasedFam`, `qpeOutFam` — the
  five stage families of the algorithm (all-`∣0⟩` input, the Hadamarded counting
  register, the kickback invariant, the Fourier state, the readout) with their
  unit-norm laws, their endpoint identities and the one-rung update step
  `qpeKickFam_step`.
* `applyOn_castSucc_H` and `iqftOp_prodV_phaseKet` — the two collapse facts the
  stages consume: the parallel Hadamard over the counting block, and the inverse
  QFT in product form.

As everywhere in this file: no program, no triple and no proof rule occurs. -/

/-! ### The phase arithmetic of the kickback -/

/-- **A phase ket does not see whole turns.** Adding an integer multiple of `2π`
to the parameter leaves `'ph θ` unchanged — the reason the kickback of a
controlled power may be computed modulo `2π`. CoqQ's `expip` periodicity
(`qtype.v`). -/
theorem phaseKet_add_int_mul_two_pi (θ : ℝ) (N : ℤ) :
    phaseKet (θ + N * (2 * Real.pi)) = phaseKet θ := by
  rw [phaseKet, phaseKet]
  congr 2
  rw [show (((θ + (N : ℝ) * (2 * Real.pi) : ℝ)) : ℂ) * Complex.I
      = ((θ : ℝ) : ℂ) * Complex.I + (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The pairing identity behind `two_pi_natVal_pow`, for one bit position `t`.
The `t`-th bit of `x` contributes to the kickback `2^i·2π·natVal x/2^n` either
*inside* the binary fraction of wire `i` (when `i ≤ t`, giving the turn
`2π/2^(t-i+1)`), or a whole number `2^(i-1-t)` of turns (when `t < i`, i.e. the
bit is more significant than the wire can resolve). Both branches are pure
algebra: the bit value `a` is an arbitrary real. Compare `qft_pair_eq` (§4). -/
private theorem qpe_pair_eq {n : ℕ} (a : ℝ) {i t : ℕ} (_hi : i < n) (ht : t < n) :
    ((2 ^ i : ℕ) : ℝ) * (2 * Real.pi * (a * 2 ^ (n - 1 - t) / 2 ^ n))
      = (if i ≤ t then a * (2 * Real.pi / 2 ^ (t - i + 1)) else 0)
        + (if i ≤ t then 0 else a * 2 ^ (i - 1 - t)) * (2 * Real.pi) := by
  push_cast
  by_cases h : i ≤ t
  · rw [if_pos h, if_pos h, zero_mul, add_zero]
    have hp : i + (n - 1 - t) + (t - i + 1) = n := by omega
    have key : (2 : ℝ) ^ i * 2 ^ (n - 1 - t) * 2 ^ (t - i + 1) = 2 ^ n := by
      rw [← pow_add, ← pow_add, hp]
    have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
    have h3 : (2 : ℝ) ^ (t - i + 1) ≠ 0 := by positivity
    field_simp
    linear_combination a * key
  · rw [if_neg h, if_neg h, zero_add]
    have hp : i + (n - 1 - t) = (i - 1 - t) + n := by omega
    have key : (2 : ℝ) ^ i * 2 ^ (n - 1 - t) = 2 ^ (i - 1 - t) * 2 ^ n := by
      rw [← pow_add, ← pow_add, hp]
    have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
    linear_combination a * key

/-- **The kickback exponent congruence.** For a phase `θ = natVal x / 2^n` and a
wire `i < n`, the angle `2^i · 2πθ` deposited on that wire by the `2^i`-th power
of the unitary is the QFT angle `qftAngle x i` **modulo `2π`**: they differ by
the integer number of turns `∑_{t < i} xₜ·2^(i-1-t)` coming from the bits above
position `i`. This is the exact-case content of CoqQ's eigenvalue hypothesis
`eigU` in `PhaseEstimation` (`example.v:980-1035`); it is the QPE analogue of
`qftAngle_sum_eq` (§4). -/
theorem two_pi_natVal_pow (n : ℕ) (x : Fin n → Bool) {i : ℕ} (hi : i < n) :
    ∃ N : ℤ, ((2 ^ i : ℕ) : ℝ) * (2 * Real.pi * ((natVal x : ℝ) / 2 ^ n))
      = qftAngle x i + N * (2 * Real.pi) := by
  classical
  refine ⟨((∑ t : Fin n,
      if (t : ℕ) < i then (if x t then 1 else 0) * 2 ^ (i - 1 - (t : ℕ)) else 0 : ℕ) : ℤ), ?_⟩
  have hlhs : ((2 ^ i : ℕ) : ℝ) * (2 * Real.pi * ((natVal x : ℝ) / 2 ^ n))
      = ∑ t : Fin n,
          ((2 ^ i : ℕ) : ℝ) * (2 * Real.pi * (bitVal (x t) * 2 ^ (n - 1 - (t : ℕ)) / 2 ^ n)) := by
    rw [natVal_cast, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
  have hK : ((((∑ t : Fin n,
        if (t : ℕ) < i then (if x t then 1 else 0) * 2 ^ (i - 1 - (t : ℕ)) else 0 : ℕ) : ℤ)) : ℝ)
      = ∑ t : Fin n, (if i ≤ (t : ℕ) then 0 else bitVal (x t) * 2 ^ (i - 1 - (t : ℕ))) := by
    rw [Int.cast_natCast, Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : i ≤ (t : ℕ)
    · rw [if_pos h, if_neg (by omega), Nat.cast_zero]
    · rw [if_neg h, if_pos (by omega)]
      cases x t <;> push_cast <;> simp [bitVal]
  have hrhs : qftAngle x i
        + (∑ t : Fin n, (if i ≤ (t : ℕ) then 0 else bitVal (x t) * 2 ^ (i - 1 - (t : ℕ))))
          * (2 * Real.pi)
      = ∑ t : Fin n,
          ((if i ≤ (t : ℕ) then bitVal (x t) * (2 * Real.pi / 2 ^ ((t : ℕ) - i + 1)) else 0)
            + (if i ≤ (t : ℕ) then 0
               else bitVal (x t) * 2 ^ (i - 1 - (t : ℕ))) * (2 * Real.pi)) := by
    rw [qftAngle, Finset.sum_mul, ← Finset.sum_add_distrib]
  rw [hlhs, hK, hrhs]
  exact Finset.sum_congr rfl fun t _ => qpe_pair_eq _ hi t.isLt

/-- **The rewrite a kickback rung ends on**: the phase ket produced by the
`2^i`-th controlled power at the exact phase `natVal x / 2^n` *is* the phase ket
of the QFT angle of wire `i`, the whole turns being invisible
(`phaseKet_add_int_mul_two_pi`). -/
theorem phaseKet_kick (n : ℕ) (x : Fin n → Bool) {i : ℕ} (hi : i < n) :
    phaseKet (((2 ^ i : ℕ) : ℝ) * (2 * Real.pi * ((natVal x : ℝ) / 2 ^ n)))
      = phaseKet (qftAngle x i) := by
  obtain ⟨N, hN⟩ := two_pi_natVal_pow n x hi
  rw [hN, phaseKet_add_int_mul_two_pi]

/-! ### The stage families -/

section QPEFamilies

variable (n : ℕ) (x : Fin n → Bool) (ψ : 𝕢)

/-- **The input family**: the `n` counting wires hold `∣0⟩`, the target wire
`Fin.last n` holds the eigenstate `ψ`. CoqQ's precondition of `RS_QPE`
(`example.v:1010`). -/
noncomputable def qpeInitFam : Fin (n + 1) → 𝕢 := fun i => if (i : ℕ) < n then q0 else ψ

/-- **After the parallel Hadamard**: the counting register is in the uniform
superposition `⊗ ∣+⟩`, the target still carries the eigenstate. -/
noncomputable def qpePlusFam : Fin (n + 1) → 𝕢 := fun i => if (i : ℕ) < n then qplus else ψ

/-- **After the whole kickback loop**: the counting register carries the Fourier
state `fourierState n x` in the product form of `fourierState_eq_prodV` (wire `i`
holds `'ph (qftAngle x (n-1-i))`), the target the eigenstate. -/
noncomputable def qpePhasedFam : Fin (n + 1) → 𝕢 :=
  fun i => if (i : ℕ) < n then phaseKet (qftAngle x (n - 1 - (i : ℕ))) else ψ

/-- **The readout family** `∣x⟩ ⊗ ∣ψ⟩`: after the inverse QFT the counting wire
`i` carries the basis ket of the bit `xᵢ`, the target is untouched. CoqQ's
postcondition of `RS_QPE_exact` (`example.v:1030`). -/
noncomputable def qpeOutFam : Fin (n + 1) → 𝕢 :=
  fun i => if h : (i : ℕ) < n then qbit (x ⟨(i : ℕ), h⟩) else ψ

/-- **The invariant of the controlled-power kickback loop**: after `m` rungs the
first `m` counting wires carry their Fourier phase, the remaining counting wires
are still `∣+⟩`, and the target still carries the eigenstate — the middle state
of CoqQ's `RS_QPE` (`example.v:1017-1021`). -/
noncomputable def qpeKickFam (m : ℕ) : Fin (n + 1) → 𝕢 :=
  fun i => if (i : ℕ) < n
    then (if (i : ℕ) < m then phaseKet (qftAngle x (n - 1 - (i : ℕ))) else qplus) else ψ

/-- Every wire of the input family is a unit vector. -/
theorem norm_qpeInitFam (hψ : ‖ψ‖ = 1) (i : Fin (n + 1)) : ‖qpeInitFam n ψ i‖ = 1 := by
  simp [qpeInitFam, hψ]

/-- Every wire of the Hadamarded family is a unit vector. -/
theorem norm_qpePlusFam (hψ : ‖ψ‖ = 1) (i : Fin (n + 1)) : ‖qpePlusFam n ψ i‖ = 1 := by
  simp [qpePlusFam, hψ]

/-- Every wire of the Fourier family is a unit vector. -/
theorem norm_qpePhasedFam (hψ : ‖ψ‖ = 1) (i : Fin (n + 1)) : ‖qpePhasedFam n x ψ i‖ = 1 := by
  simp [qpePhasedFam, hψ]

/-- Every wire of the readout family is a unit vector. -/
theorem norm_qpeOutFam (hψ : ‖ψ‖ = 1) (i : Fin (n + 1)) : ‖qpeOutFam n x ψ i‖ = 1 := by
  simp [qpeOutFam, hψ]

/-- Every wire of the kickback invariant is a unit vector. -/
theorem norm_qpeKickFam (hψ : ‖ψ‖ = 1) (m : ℕ) (i : Fin (n + 1)) :
    ‖qpeKickFam n x ψ m i‖ = 1 := by
  simp [qpeKickFam, hψ]

/-- **Start of the kickback loop**: before the first controlled power the
counting register is still the uniform superposition. -/
theorem qpeKickFam_zero : qpeKickFam n x ψ 0 = qpePlusFam n ψ := by
  funext i
  simp [qpeKickFam, qpePlusFam]

/-- **End of the kickback loop**: after `n` controlled powers the counting
register carries the Fourier state of `x`. -/
theorem qpeKickFam_full : qpeKickFam n x ψ n = qpePhasedFam n x ψ := by
  funext i
  simp only [qpeKickFam, qpePhasedFam]
  by_cases h : (i : ℕ) < n
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- The control wire of the `k`-th rung is exactly the one the invariant has not
yet phased. -/
theorem qpeKickFam_ctrl (k : Fin n) : qpeKickFam n x ψ (k : ℕ) k.castSucc = qplus := by
  simp only [qpeKickFam, Fin.val_castSucc]
  rw [if_pos k.isLt, if_neg (lt_irrefl _)]

/-- The target wire carries the eigenstate at every stage of the loop: no rung
changes it (the eigenvalue equation is what turns each controlled power into a
phase on the control). -/
theorem qpeKickFam_last (m : ℕ) : qpeKickFam n x ψ m (Fin.last n) = ψ := by
  simp only [qpeKickFam, Fin.val_last]
  rw [if_neg (lt_irrefl _)]

/-- **One rung of the kickback loop.** Phasing the `k`-th counting wire by its
QFT angle and writing the eigenstate back on the target lands exactly on the next
stage of the invariant. This is the state-algebra content of one controlled
power; the arithmetic that produces the angle is `phaseKet_kick`. -/
theorem qpeKickFam_step (k : Fin n) :
    Function.update (Function.update (qpeKickFam n x ψ (k : ℕ)) k.castSucc
        (phaseKet (qftAngle x (n - 1 - (k : ℕ))))) (Fin.last n) ψ
      = qpeKickFam n x ψ ((k : ℕ) + 1) := by
  funext i
  by_cases hlast : i = Fin.last n
  · rw [hlast, Function.update_self]
    exact (qpeKickFam_last n x ψ _).symm
  · rw [Function.update_of_ne hlast]
    have hin : (i : ℕ) < n := by
      have h1 := i.isLt
      have h2 : (i : ℕ) ≠ n := fun hc => hlast (Fin.ext (by rw [Fin.val_last]; exact hc))
      omega
    by_cases hk : i = k.castSucc
    · rw [hk, Function.update_self]
      simp only [qpeKickFam, Fin.val_castSucc]
      rw [if_pos k.isLt, if_pos (Nat.lt_succ_self _)]
    · rw [Function.update_of_ne hk]
      have hik : (i : ℕ) ≠ (k : ℕ) := fun hc =>
        hk (Fin.ext (by rw [Fin.val_castSucc]; exact hc))
      simp only [qpeKickFam]
      rw [if_pos hin, if_pos hin]
      by_cases hlt : (i : ℕ) < (k : ℕ)
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

/-- A counting wire of the Fourier family. -/
theorem qpePhasedFam_castSucc (j : Fin n) :
    qpePhasedFam n x ψ j.castSucc = phaseKet (qftAngle x (n - 1 - (j : ℕ))) := by
  simp only [qpePhasedFam, Fin.val_castSucc]
  rw [if_pos j.isLt]

/-- A counting wire of the readout family: the basis ket of its own bit. -/
theorem qpeOutFam_castSucc (j : Fin n) : qpeOutFam n x ψ j.castSucc = qbit (x j) := by
  have h : ((j.castSucc : Fin (n + 1)) : ℕ) < n := by rw [Fin.val_castSucc]; exact j.isLt
  rw [qpeOutFam, dif_pos h]
  exact congrArg (fun b => qbit (x b)) (Fin.ext (Fin.val_castSucc j))

/-- The target wire of the Fourier family is the eigenstate. -/
theorem qpePhasedFam_last : qpePhasedFam n x ψ (Fin.last n) = ψ := by
  simp only [qpePhasedFam, Fin.val_last]
  rw [if_neg (lt_irrefl _)]

/-- The target wire of the readout family is the eigenstate: phase estimation
returns its eigenvector untouched. -/
theorem qpeOutFam_last : qpeOutFam n x ψ (Fin.last n) = ψ := by
  simp only [qpeOutFam, Fin.val_last]
  rw [dif_neg (lt_irrefl _)]

end QPEFamilies

/-! ### The preparation-loop invariant -/

section QPEPrepFamily

variable (n : ℕ) (ψ : 𝕢)

/-- **The invariant of the preparation loop**: `∣+⟩^m ⊗ ∣0⟩^{n-m} ⊗ ∣ψ⟩` —
after `m` passes the first `m` counting wires are Hadamarded, the remaining
counting wires still hold `∣0⟩`, the target still carries the eigenstate. The
prefix interpolant of the Hadamard layer with the target framed, the exact
analogue of the kickback invariant `qpeKickFam` one stage earlier. -/
noncomputable def qpePrepFam (m : ℕ) : Fin (n + 1) → 𝕢 :=
  fun i => if (i : ℕ) < n then (if (i : ℕ) < m then qplus else q0) else ψ

/-- Every wire of the preparation invariant is a unit vector. -/
theorem norm_qpePrepFam (hψ : ‖ψ‖ = 1) (m : ℕ) (i : Fin (n + 1)) :
    ‖qpePrepFam n ψ m i‖ = 1 := by
  simp [qpePrepFam, hψ]

/-- **Start of the preparation loop**: no wire Hadamarded yet. -/
theorem qpePrepFam_zero : qpePrepFam n ψ 0 = qpeInitFam n ψ := by
  funext i
  simp [qpePrepFam, qpeInitFam]

/-- **End of the preparation loop**: the whole counting register is in the
uniform superposition. -/
theorem qpePrepFam_full : qpePrepFam n ψ n = qpePlusFam n ψ := by
  funext i
  simp only [qpePrepFam, qpePlusFam]
  by_cases h : (i : ℕ) < n
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- The wire of the `k`-th pass is exactly the one the invariant has not yet
Hadamarded. -/
theorem qpePrepFam_ctrl (k : Fin n) : qpePrepFam n ψ (k : ℕ) k.castSucc = q0 := by
  simp only [qpePrepFam, Fin.val_castSucc]
  rw [if_pos k.isLt, if_neg (lt_irrefl _)]

/-- The target wire carries the eigenstate at every stage of the loop. -/
theorem qpePrepFam_last (m : ℕ) : qpePrepFam n ψ m (Fin.last n) = ψ := by
  simp only [qpePrepFam, Fin.val_last]
  rw [if_neg (lt_irrefl _)]

/-- **One pass of the preparation loop**: Hadamarding the `k`-th counting wire
lands exactly on the next stage of the invariant. -/
theorem qpePrepFam_step (k : Fin n) :
    Function.update (qpePrepFam n ψ (k : ℕ)) k.castSucc qplus
      = qpePrepFam n ψ ((k : ℕ) + 1) := by
  funext i
  by_cases hk : i = k.castSucc
  · rw [hk, Function.update_self]
    simp only [qpePrepFam, Fin.val_castSucc]
    rw [if_pos k.isLt, if_pos (Nat.lt_succ_self _)]
  · rw [Function.update_of_ne hk]
    have hik : (i : ℕ) ≠ (k : ℕ) := fun hc =>
      hk (Fin.ext (by rw [Fin.val_castSucc]; exact hc))
    simp only [qpePrepFam]
    by_cases hin : (i : ℕ) < n
    · rw [if_pos hin, if_pos hin]
      by_cases hlt : (i : ℕ) < (k : ℕ)
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]
    · rw [if_neg hin, if_neg hin]

end QPEPrepFamily

/-! ### The two collapse facts -/

/-- **The parallel Hadamard over the counting block.** Applying `H` at every
cell `Fin.castSucc k` of the `(n+1)`-qubit world — and at no other cell — turns
the input family into the Hadamarded one: the target `Fin.last n` is not in the
loop list, so its eigenstate survives. CoqQ's `RS_ParaHadamard_tuple`
consumed by `PhaseEstimation` (`example.v:1013`). -/
theorem applyOn_castSucc_H (n : ℕ) (ψ : 𝕢) :
    applyOn (D := QubitD (n + 1)) ((List.finRange n).map Fin.castSucc) (fun _ => H)
        (qpeInitFam n ψ)
      = qpePlusFam n ψ := by
  funext i
  have hmem : i ∈ (List.finRange n).map Fin.castSucc ↔ (i : ℕ) < n := by
    constructor
    · intro h
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
      rw [Fin.val_castSucc]
      exact j.isLt
    · intro h
      exact List.mem_map.mpr ⟨⟨(i : ℕ), h⟩, List.mem_finRange _, Fin.ext rfl⟩
  simp only [applyOn, qpeInitFam, qpePlusFam]
  by_cases h : (i : ℕ) < n
  · rw [if_pos (hmem.mpr h), if_pos h, if_pos h, H_q0]
  · rw [if_neg (fun hc => h (hmem.mp hc)), if_neg h, if_neg h]

/-- **The inverse-QFT readout in product form.** The IQFT maps the product of
phase kets `⊗ⱼ 'ph (qftAngle x (n-1-j))` — which *is* the Fourier state
(`fourierState_eq_prodV`, CoqQ `QFTbv_rev`) — to the product of basis kets
`⊗ⱼ ∣xⱼ⟩`. This is CoqQ's `IQFTEt` (`qtype.v`) in the shape the phase-estimation
readout stage transports onto the counting block. -/
theorem iqftOp_prodV_phaseKet (n : ℕ) (x : Fin n → Bool) :
    (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n)))
        (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          fun j => phaseKet (qftAngle x (n - 1 - (j : ℕ))))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n))) fun j => qbit (x j) := by
  rw [← fourierState_eq_prodV, iqftOp_fourierState]
  exact (prodV_single (QubitD n) fun i => x i).symm

/-! ## §12. The QPE stage algebra at an arbitrary real phase

The **inexact** counterpart of §11.  Nothing changes in the *shape* of the
kickback: the `k`-th rung deposits the angle `2π·2^{n-1-k}·φ` on its control
wire whatever the real phase `φ` is — it is only the *readout* that stops being
exact when `φ` is not an `n`-bit dyadic.  So the stage families below are
literally §11's with the exact-case angle `qftAngle x (n-1-i)` replaced by the
raw deposited angle `2π·(2^{n-1-i}·φ)`; the loop laws (`qpeKickFamR_zero`,
`_full`, `_ctrl`, `_last`, `_step`) are proved exactly as in §11, since they are
pure `if`-algebra in the wire index and never look at the phase.

The wire angle is chosen byte-identically to `qpeKickedKet`
(`Qhl/Register/QPEPrecisionBridge.lean`), so that the counting block of
`qpePhasedFamR` **is** the kicked profile whose Fourier overlaps the N&C §5.2.1
precision analysis bounds (`prodV_qpePhasedFamR_castSucc`).  At an exact dyadic
phase `φ = natVal x / 2^n` these families agree wire-by-wire with §11's
(`phaseKet_kick`).

As everywhere in this file: no program, no triple and no proof rule occurs. -/

section QPEFamiliesReal

variable (n : ℕ) (φ : ℝ) (ψ : 𝕢)

/-- **The stage-2 family at an arbitrary real phase**: every counting wire `i`
carries the phase ket of the angle `2π·2^{n-1-i}·φ` deposited by the controlled
`2^{n-1-i}`-th power, the target wire the eigenstate.  The inexact-phase analogue
of `qpePhasedFam`; at `φ = natVal x / 2^n` the two agree (`phaseKet_kick`). -/
noncomputable def qpePhasedFamR (n : ℕ) (φ : ℝ) (ψ : 𝕢) : Fin (n + 1) → 𝕢 :=
  fun i => if (i : ℕ) < n
    then phaseKet (2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (i : ℕ)) * φ)) else ψ

/-- **The kickback-loop invariant at an arbitrary real phase**: after `m` rungs
the first `m` counting wires carry their deposited phase, the remaining counting
wires are still `∣+⟩`, and the target still carries the eigenstate.  The
inexact-phase analogue of `qpeKickFam`. -/
noncomputable def qpeKickFamR (n : ℕ) (φ : ℝ) (ψ : 𝕢) (m : ℕ) : Fin (n + 1) → 𝕢 :=
  fun i => if (i : ℕ) < n
    then (if (i : ℕ) < m
      then phaseKet (2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (i : ℕ)) * φ)) else qplus)
    else ψ

/-- Every wire of the real-phase stage-2 family is a unit vector. -/
theorem norm_qpePhasedFamR (hψ : ‖ψ‖ = 1) (i : Fin (n + 1)) :
    ‖qpePhasedFamR n φ ψ i‖ = 1 := by
  simp [qpePhasedFamR, hψ]

/-- Every wire of the real-phase kickback invariant is a unit vector. -/
theorem norm_qpeKickFamR (hψ : ‖ψ‖ = 1) (m : ℕ) (i : Fin (n + 1)) :
    ‖qpeKickFamR n φ ψ m i‖ = 1 := by
  simp [qpeKickFamR, hψ]

/-- **Start of the real-phase kickback loop**: before the first controlled power
the counting register is still the uniform superposition. -/
theorem qpeKickFamR_zero : qpeKickFamR n φ ψ 0 = qpePlusFam n ψ := by
  funext i
  simp [qpeKickFamR, qpePlusFam]

/-- **End of the real-phase kickback loop**: after `n` controlled powers every
counting wire carries its deposited phase. -/
theorem qpeKickFamR_full : qpeKickFamR n φ ψ n = qpePhasedFamR n φ ψ := by
  funext i
  simp only [qpeKickFamR, qpePhasedFamR]
  by_cases h : (i : ℕ) < n
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- The control wire of the `k`-th rung is exactly the one the invariant has not
yet phased. -/
theorem qpeKickFamR_ctrl (k : Fin n) : qpeKickFamR n φ ψ (k : ℕ) k.castSucc = qplus := by
  simp only [qpeKickFamR, Fin.val_castSucc]
  rw [if_pos k.isLt, if_neg (lt_irrefl _)]

/-- The target wire carries the eigenstate at every stage of the loop: no rung
changes it. -/
theorem qpeKickFamR_last (m : ℕ) : qpeKickFamR n φ ψ m (Fin.last n) = ψ := by
  simp only [qpeKickFamR, Fin.val_last]
  rw [if_neg (lt_irrefl _)]

/-- **One rung of the real-phase kickback loop.**  Phasing the `k`-th counting
wire by the angle its controlled power deposits and writing the eigenstate back
on the target lands exactly on the next stage of the invariant.  This is the
state-algebra content of one controlled power at an *arbitrary* phase — no
dyadic arithmetic is involved, which is exactly why the inexact case reuses the
same loop rule. -/
theorem qpeKickFamR_step (k : Fin n) :
    Function.update (Function.update (qpeKickFamR n φ ψ (k : ℕ)) k.castSucc
        (phaseKet (2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (k : ℕ)) * φ)))) (Fin.last n) ψ
      = qpeKickFamR n φ ψ ((k : ℕ) + 1) := by
  funext i
  by_cases hlast : i = Fin.last n
  · rw [hlast, Function.update_self]
    exact (qpeKickFamR_last n φ ψ _).symm
  · rw [Function.update_of_ne hlast]
    have hin : (i : ℕ) < n := by
      have h1 := i.isLt
      have h2 : (i : ℕ) ≠ n := fun hc => hlast (Fin.ext (by rw [Fin.val_last]; exact hc))
      omega
    by_cases hk : i = k.castSucc
    · rw [hk, Function.update_self]
      simp only [qpeKickFamR, Fin.val_castSucc]
      rw [if_pos k.isLt, if_pos (Nat.lt_succ_self _)]
    · rw [Function.update_of_ne hk]
      have hik : (i : ℕ) ≠ (k : ℕ) := fun hc =>
        hk (Fin.ext (by rw [Fin.val_castSucc]; exact hc))
      simp only [qpeKickFamR]
      rw [if_pos hin, if_pos hin]
      by_cases hlt : (i : ℕ) < (k : ℕ)
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

/-- A counting wire of the real-phase stage-2 family. -/
theorem qpePhasedFamR_castSucc (j : Fin n) :
    qpePhasedFamR n φ ψ j.castSucc
      = phaseKet (2 * Real.pi * ((2 : ℝ) ^ (n - 1 - (j : ℕ)) * φ)) := by
  simp only [qpePhasedFamR, Fin.val_castSucc]
  rw [if_pos j.isLt]

/-- The target wire of the real-phase stage-2 family is the eigenstate. -/
theorem qpePhasedFamR_last : qpePhasedFamR n φ ψ (Fin.last n) = ψ := by
  simp only [qpePhasedFamR, Fin.val_last]
  rw [if_neg (lt_irrefl _)]

end QPEFamiliesReal

end Qhl
