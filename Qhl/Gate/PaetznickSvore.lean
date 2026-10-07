import Qhl.Gate.ControlledU
import Qhl.Gate.Rx
import Qhl.Gate.HeraldedBlock

/-!
# The Paetznick–Svore two-`T` repeat-until-success block (their Fig. 8)

The gate-level layer of the smallest repeat-until-success circuit in the
Paetznick–Svore database (arXiv:1311.1074, Fig. 8): one ancilla qubit, two `T`
gates, two `CNOT`s and three Hadamards. Reading the circuit left to right on
the ancilla wire — `H, T, •, H, •, T, H` with the two `CNOT`s targeting the
data wire — and with the ancilla as the **first** factor of
`EuclideanSpace ℂ (Bool × Bool)` (the composition convention of
`Qhl/Gate/RUSBlock.lean`: the rightmost factor of the product applies first):

```
wPS := (H ⊗ 1) · (T ⊗ 1) · CNOT · (H ⊗ 1) · CNOT · (T ⊗ 1) · (H ⊗ 1).
```

A computational-basis measurement of the ancilla then yields

* outcome `0` (probability `3/4`): the data has undergone the non-Clifford
  unitary `V = (1 + i√2 X)/√3` (`vPS` below);
* outcome `1` (probability `1/4`): the data is exactly unchanged, ready for
  another repetition.

The single quantum fact a repeat-until-success verification needs is the
branch decomposition `wPS_decomp`:

```
wPS (∣0⟩ ⊗ χ) = α · ∣0⟩ ⊗ (V χ) + β · ∣1⟩ ⊗ χ,
α = (√3/2)·e^{-iπ/4},  β = (1/2)·e^{iπ/4},  |α|² = 3/4,  |β|² = 1/4,
```

proved on the basis kets by the named-action-lemma chains of the gate layer
(`fstU_vpair`, `H_q0`/`H_q1`, `T_q0`/`T_q1`, `CNOT_vpair`) — no matrix entry
of the composite is ever evaluated — and extended to every `χ` by
`qubit_decomp` and linearity.

Everything here is gate algebra only (ownership test): no program, register,
or Hoare triple appears.
-/

namespace Qhl

open scoped Matrix

/-! ## Square-root scalar helpers -/

/-- `√2` is nonzero in `ℂ`. -/
theorem sqrt_two_ne_zero' : (Real.sqrt 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (by positivity)

/-- `√3` is nonzero in `ℂ`. -/
theorem sqrt_three_ne_zero' : (Real.sqrt 3 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (by positivity)

/-- `√2 · √2 = 2` in `ℂ`. -/
theorem sqrt_two_mul_self' : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- `√3 · (√3)⁻¹ = 1` in `ℂ`. -/
theorem sqrt_three_mul_inv : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ = 1 :=
  mul_inv_cancel₀ sqrt_three_ne_zero'

/-- `√2 · (√2)⁻¹ = 1` in `ℂ`. -/
theorem sqrt_two_mul_inv : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)⁻¹ = 1 :=
  mul_inv_cancel₀ sqrt_two_ne_zero'

/-- `(√3)⁻¹ · (√3)⁻¹ = 3⁻¹` in `ℂ`, the mirror of `inv_sqrt_two_mul_self`. -/
theorem inv_sqrt_three_mul_self :
    (Real.sqrt 3 : ℂ)⁻¹ * (Real.sqrt 3 : ℂ)⁻¹ = 3⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- `√2/2 = (√2)⁻¹` in `ℂ`, the coordinate form `cos (π/4)` takes. -/
theorem sqrt_two_div_two : ((Real.sqrt 2 / 2 : ℝ) : ℂ) = (Real.sqrt 2 : ℂ)⁻¹ := by
  push_cast
  field_simp
  rw [pow_two]
  exact sqrt_two_mul_self'

/-! ## The eighth root of unity `ω = e^{iπ/4}`

The `T`-gate phase. Its square is `i`, its conjugate is its inverse
`e^{-iπ/4}`, and in coordinates `ω = (1 + i)/√2`. -/

/-- `ω = e^{iπ/4}`, the `T`-gate phase. -/
noncomputable def omega : ℂ := Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- `ω` in coordinates: `(1 + i)/√2`. -/
theorem omega_eq : omega = (Real.sqrt 2 : ℂ)⁻¹ * (1 + Complex.I) := by
  rw [omega, exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four,
    sqrt_two_div_two]
  ring

@[simp]
theorem norm_omega : ‖omega‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- `ω² = i`: two `T` phases make an `S` phase. -/
theorem omega_sq : omega ^ 2 = Complex.I := by
  rw [sq, omega_eq]
  linear_combination ((1 + Complex.I) ^ 2) * inv_sqrt_two_mul_self
    + (2⁻¹ : ℂ) * Complex.I_sq

/-- The conjugate of `ω` in coordinates: `(1 - i)/√2`. -/
theorem star_omega_eq : star omega = (Real.sqrt 2 : ℂ)⁻¹ * (1 - Complex.I) := by
  rw [omega_eq, star_mul', star_add, star_one, star_inv_sqrt_two, RCLike.star_def,
    Complex.conj_I]
  ring

/-- The conjugate of `ω` is `e^{-iπ/4}`. -/
theorem star_omega : star omega = Complex.exp (((-(Real.pi / 4) : ℝ)) * Complex.I) := by
  rw [omega, RCLike.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `ω · ω̄ = 1`: `ω` has unit modulus. -/
theorem omega_mul_star_omega : omega * star omega = 1 := by
  rw [star_omega_eq, omega_eq]
  linear_combination (1 - Complex.I ^ 2) * inv_sqrt_two_mul_self
    - (2⁻¹ : ℂ) * Complex.I_sq

/-- The conjugate of `ω` is its inverse. -/
theorem omega_inv : omega⁻¹ = star omega :=
  inv_eq_of_mul_eq_one_right omega_mul_star_omega

/-- `ω̄ · i = ω`: a quarter turn past `e^{-iπ/4}` is `e^{iπ/4}`. -/
theorem star_omega_mul_I : star omega * Complex.I = omega := by
  rw [star_omega_eq, omega_eq]
  linear_combination (-(Real.sqrt 2 : ℂ)⁻¹) * Complex.I_sq

/-- The `T` action on `∣1⟩`, with the phase named `ω`. -/
theorem T_q1_omega : (T : 𝕢 →ₗ[ℂ] 𝕢) q1 = omega • q1 := T_q1

/-! ## The success unitary `V = (1 + i√2 X)/√3` -/

/-- The matrix of `V = (1 + i√2 X)/√3`: diagonal entries `1/√3`, off-diagonal
entries `i√2/√3`. -/
noncomputable def vMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    (Real.sqrt 3 : ℂ)⁻¹ * (if a = b then 1 else Complex.I * (Real.sqrt 2 : ℂ))

/-- The Paetznick–Svore success unitary `V = (1 + i√2 X)/√3` (their Fig. 8:
the operation the circuit implements on measuring `0`). -/
noncomputable def vPS : UnitaryOp 𝕢 :=
  unitaryOfMat vMat <| by
    have h2 := sqrt_two_mul_self'
    have h3 := inv_sqrt_three_mul_self
    ext i j
    cases i <;> cases j <;>
      simp only [vMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Fintype.sum_bool, Matrix.one_apply, reduceIte, Bool.false_eq_true,
        Bool.true_eq_false, RCLike.star_def, map_mul, map_one, map_inv₀,
        Complex.conj_ofReal, Complex.conj_I]
    · linear_combination (3 : ℂ) * h3
        - ((Real.sqrt 3 : ℂ)⁻¹ ^ 2 * (Real.sqrt 2 : ℂ) ^ 2) * Complex.I_sq
        + ((Real.sqrt 3 : ℂ)⁻¹ ^ 2) * h2
    · ring
    · ring
    · linear_combination (3 : ℂ) * h3
        - ((Real.sqrt 3 : ℂ)⁻¹ ^ 2 * (Real.sqrt 2 : ℂ) ^ 2) * Complex.I_sq
        + ((Real.sqrt 3 : ℂ)⁻¹ ^ 2) * h2

/-- The `V` action on `∣0⟩`: `V∣0⟩ = (∣0⟩ + i√2 ∣1⟩)/√3`. -/
theorem vPS_q0 :
    (vPS : 𝕢 →ₗ[ℂ] 𝕢) q0
      = (Real.sqrt 3 : ℂ)⁻¹ • (q0 + (Complex.I * (Real.sqrt 2 : ℂ)) • q1) := by
  ext b
  rw [show ((vPS : 𝕢 →ₗ[ℂ] 𝕢)) = matOp vMat from rfl, matOp_apply, Fintype.sum_bool]
  cases b <;>
    simp only [vMat, Matrix.of_apply, PiLp.smul_apply, PiLp.add_apply, q0_apply, q1_apply,
      smul_eq_mul, reduceIte, Bool.false_eq_true, Bool.true_eq_false] <;>
    ring

/-- The `V` action on `∣1⟩`: `V∣1⟩ = (i√2 ∣0⟩ + ∣1⟩)/√3`. -/
theorem vPS_q1 :
    (vPS : 𝕢 →ₗ[ℂ] 𝕢) q1
      = (Real.sqrt 3 : ℂ)⁻¹ • ((Complex.I * (Real.sqrt 2 : ℂ)) • q0 + q1) := by
  ext b
  rw [show ((vPS : 𝕢 →ₗ[ℂ] 𝕢)) = matOp vMat from rfl, matOp_apply, Fintype.sum_bool]
  cases b <;>
    simp only [vMat, Matrix.of_apply, PiLp.smul_apply, PiLp.add_apply, q0_apply, q1_apply,
      smul_eq_mul, reduceIte, Bool.false_eq_true, Bool.true_eq_false] <;>
    ring

/-! ## Private right-factor and basis-ket helpers

The library's `vpair` linearity lemmas cover the left factor
(`vpair_smul_left`/`vpair_add_left`) and, through `Qhl/Gate/HeraldedBlock.lean`,
the right-factor addition (`vpair_add_right`); this file also needs a
right-factor scalar law and a subtraction form, plus the four `CNOT` basis
actions with `q0`/`q1` in place of `qbit`. Those are kept `private` local
copies. -/

private theorem psLocal_vpair_sub_left {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (u u' : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) :
    vpair (u - u') v = vpair u v - vpair u' v := by
  ext p
  simp only [vpair_apply, PiLp.sub_apply]
  ring

private theorem psLocal_vpair_smul_right {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (c : ℂ) (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) :
    vpair u (c • v) = c • vpair u v := by
  ext p
  simp only [vpair_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem psLocal_CNOT_00 :
    (CNOT : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
      (vpair q0 q0) = vpair q0 q0 := by
  simpa using CNOT_vpair false false

private theorem psLocal_CNOT_01 :
    (CNOT : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
      (vpair q0 q1) = vpair q0 q1 := by
  simpa using CNOT_vpair false true

private theorem psLocal_CNOT_10 :
    (CNOT : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
      (vpair q1 q0) = vpair q1 q1 := by
  simpa using CNOT_vpair true false

private theorem psLocal_CNOT_11 :
    (CNOT : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
      (vpair q1 q1) = vpair q1 q0 := by
  simpa using CNOT_vpair true true

/-! ## The Fig. 8 repeated circuit `wPS` -/

/-- The Paetznick–Svore Fig. 8 repeated circuit, ancilla first: the circuit
`H, T, CNOT, H, CNOT, T, H` on the ancilla wire (the two `CNOT`s controlled by
the ancilla, targeting the data), composed so the rightmost factor applies
first — the circuit's left-to-right order. -/
noncomputable def wPS : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)) :=
  fstU H * fstU T * CNOT * fstU H * CNOT * fstU T * fstU H

/-- The block action on `∣0⟩ ⊗ ∣0⟩`:
`wPS(∣00⟩) = (ω̄/2)∣00⟩ + (ω/√2)∣01⟩ + (ω/2)∣10⟩`. -/
theorem wPS_vpair_q0_q0 :
    (wPS : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair q0 q0)
      = (star omega * 2⁻¹) • vpair q0 q0
        + (omega * (Real.sqrt 2 : ℂ)⁻¹) • vpair q0 q1
        + (omega * 2⁻¹) • vpair q1 q0 := by
  simp only [wPS, UnitaryOp.coe_mul, LinearMap.comp_apply, map_smul, map_add, map_sub,
    fstU_vpair, H_q0, H_q1, T_q0, T_q1_omega, qplus, qminus, vpair_smul_left,
    vpair_add_left, psLocal_vpair_sub_left, psLocal_CNOT_00, psLocal_CNOT_01,
    psLocal_CNOT_10, psLocal_CNOT_11]
  rw [star_omega_eq, omega_eq]
  match_scalars
  · linear_combination ((Real.sqrt 2 : ℂ)⁻¹
        - 2 * Complex.I * (Real.sqrt 2 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ)⁻¹ ^ 2 + 2⁻¹))
        * inv_sqrt_two_mul_self
      - (Real.sqrt 2 : ℂ)⁻¹ ^ 5 * Complex.I_sq
  · linear_combination ((Real.sqrt 2 : ℂ)⁻¹
        + 2 * Complex.I * (Real.sqrt 2 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ)⁻¹ ^ 2 + 2⁻¹))
        * inv_sqrt_two_mul_self
      + (Real.sqrt 2 : ℂ)⁻¹ ^ 5 * Complex.I_sq
  · linear_combination (2 * (Real.sqrt 2 : ℂ)⁻¹ ^ 2 * (1 + Complex.I))
        * inv_sqrt_two_mul_self
  · ring

/-- The block action on `∣0⟩ ⊗ ∣1⟩`:
`wPS(∣01⟩) = (ω/√2)∣00⟩ + (ω̄/2)∣01⟩ + (ω/2)∣11⟩`. -/
theorem wPS_vpair_q0_q1 :
    (wPS : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair q0 q1)
      = (omega * (Real.sqrt 2 : ℂ)⁻¹) • vpair q0 q0
        + (star omega * 2⁻¹) • vpair q0 q1
        + (omega * 2⁻¹) • vpair q1 q1 := by
  simp only [wPS, UnitaryOp.coe_mul, LinearMap.comp_apply, map_smul, map_add, map_sub,
    fstU_vpair, H_q0, H_q1, T_q0, T_q1_omega, qplus, qminus, vpair_smul_left,
    vpair_add_left, psLocal_vpair_sub_left, psLocal_CNOT_00, psLocal_CNOT_01,
    psLocal_CNOT_10, psLocal_CNOT_11]
  rw [star_omega_eq, omega_eq]
  match_scalars
  · linear_combination ((Real.sqrt 2 : ℂ)⁻¹
        - 2 * Complex.I * (Real.sqrt 2 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ)⁻¹ ^ 2 + 2⁻¹))
        * inv_sqrt_two_mul_self
      - (Real.sqrt 2 : ℂ)⁻¹ ^ 5 * Complex.I_sq
  · linear_combination ((Real.sqrt 2 : ℂ)⁻¹
        + 2 * Complex.I * (Real.sqrt 2 : ℂ)⁻¹ * ((Real.sqrt 2 : ℂ)⁻¹ ^ 2 + 2⁻¹))
        * inv_sqrt_two_mul_self
      + (Real.sqrt 2 : ℂ)⁻¹ ^ 5 * Complex.I_sq
  · linear_combination (2 * (Real.sqrt 2 : ℂ)⁻¹ ^ 2 * (1 + Complex.I))
        * inv_sqrt_two_mul_self
  · ring

/-! ## The branch amplitudes -/

/-- The success amplitude `α = (√3/2)·e^{-iπ/4}`: `|α|² = 3/4`. -/
noncomputable def alphaPS : ℂ :=
  ((Real.sqrt 3 : ℂ) / 2) * Complex.exp (((-(Real.pi / 4) : ℝ)) * Complex.I)

/-- The failure amplitude `β = (1/2)·e^{iπ/4}`: `|β|² = 1/4`. -/
noncomputable def betaPS : ℂ :=
  (2 : ℂ)⁻¹ * Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- `α` through the conjugate phase: `α = (√3/2)·ω̄`. -/
theorem alphaPS_eq_star : alphaPS = ((Real.sqrt 3 : ℂ) / 2) * star omega := by
  rw [alphaPS, star_omega]

/-- `β` through the phase: `β = ω/2`. -/
theorem betaPS_eq_omega : betaPS = omega * 2⁻¹ := by
  rw [betaPS, omega]
  ring

/-- `|α|² = 3/4`: the success probability of the Fig. 8 block. -/
theorem normSq_alphaPS : ‖alphaPS‖ ^ 2 = 3 / 4 := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [alphaPS, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 3), h2]
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- `|β|² = 1/4`: the failure probability of the Fig. 8 block. -/
theorem normSq_betaPS : ‖betaPS‖ ^ 2 = 1 / 4 := by
  rw [betaPS, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_inv]
  norm_num

/-! ## The branch decomposition -/

private theorem wPS_decomp_q0 :
    (wPS : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair q0 q0)
      = alphaPS • vpair q0 ((vPS : 𝕢 →ₗ[ℂ] 𝕢) q0) + betaPS • vpair q1 q0 := by
  rw [wPS_vpair_q0_q0, vPS_q0, psLocal_vpair_smul_right, vpair_add_right,
    psLocal_vpair_smul_right, alphaPS_eq_star, betaPS_eq_omega, star_omega_eq, omega_eq]
  match_scalars
  · linear_combination (-((Real.sqrt 2 : ℂ)⁻¹ * (1 - Complex.I)) * 2⁻¹)
        * sqrt_three_mul_inv
  · linear_combination (1 + Complex.I) * inv_sqrt_two_mul_self
      - ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)⁻¹ * (Complex.I - Complex.I ^ 2) * 2⁻¹)
        * sqrt_three_mul_inv
      - ((Complex.I - Complex.I ^ 2) * 2⁻¹) * sqrt_two_mul_inv
      + (2⁻¹ : ℂ) * Complex.I_sq
  · ring

private theorem wPS_decomp_q1 :
    (wPS : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair q0 q1)
      = alphaPS • vpair q0 ((vPS : 𝕢 →ₗ[ℂ] 𝕢) q1) + betaPS • vpair q1 q1 := by
  rw [wPS_vpair_q0_q1, vPS_q1, psLocal_vpair_smul_right, vpair_add_right,
    psLocal_vpair_smul_right, alphaPS_eq_star, betaPS_eq_omega, star_omega_eq, omega_eq]
  match_scalars
  · linear_combination (1 + Complex.I) * inv_sqrt_two_mul_self
      - ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)⁻¹ * (Complex.I - Complex.I ^ 2) * 2⁻¹)
        * sqrt_three_mul_inv
      - ((Complex.I - Complex.I ^ 2) * 2⁻¹) * sqrt_two_mul_inv
      + (2⁻¹ : ℂ) * Complex.I_sq
  · linear_combination (-((Real.sqrt 2 : ℂ)⁻¹ * (1 - Complex.I)) * 2⁻¹)
        * sqrt_three_mul_inv
  · ring

/-- **The Paetznick–Svore branch decomposition** (their Fig. 8): on an ancilla
prepared in `∣0⟩`, the repeated circuit splits every data state `χ` into the
measurement branches

```
wPS (∣0⟩ ⊗ χ) = α · ∣0⟩ ⊗ (V χ) + β · ∣1⟩ ⊗ χ,
```

with `α = (√3/2)e^{-iπ/4}` (success: `V` applied, ancilla reads `0`,
probability `|α|² = 3/4`) and `β = (1/2)e^{iπ/4}` (failure: data exactly
unchanged, ancilla reads `1`, probability `|β|² = 1/4`). Proved on the basis
kets by the gate-action chains and extended by `qubit_decomp` and linearity. -/
theorem wPS_decomp (χ : 𝕢) :
    (wPS : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair q0 χ)
      = alphaPS • vpair q0 ((vPS : 𝕢 →ₗ[ℂ] 𝕢) χ) + betaPS • vpair q1 χ := by
  rw [qubit_decomp χ]
  simp only [vpair_add_right, psLocal_vpair_smul_right, map_add, map_smul,
    wPS_decomp_q0, wPS_decomp_q1]
  module

end Qhl
