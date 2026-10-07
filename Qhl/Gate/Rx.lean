import Qhl.Gate.Rzz

/-!
# The `x`-rotation on the diagonal (`±`) basis

The gate-atom layer of the transverse-field term `a j · X_j`: the `x`-rotation
`Rx θ = e^{-i(θ/2)X}` (`Qhl/Gate/Qubit.lean`) is **diagonal in the `±` basis**,

```
Rx θ ∣+⟩ = e^{-iθ/2} ∣+⟩,      Rx θ ∣-⟩ = e^{+iθ/2} ∣-⟩,
```

because `∣±⟩` are the `X`-eigenvectors with eigenvalues `±1`. With the
eigenvalue function `zsign` (`z(false) = 1`, `z(true) = -1`, shared with the
`Rz`/`Rzz` convention of `Qhl/Gate/Rzz.lean`) and the basis family
`pmKet false = ∣+⟩`, `pmKet true = ∣-⟩`, the two actions combine into the
single law

```
Rx θ (pmKet b) = e^{-i(θ/2)·z(b)} (pmKet b)      (`Rx_pmKet`),
```

the exact `±`-basis analogue of `Rz_single` on the computational basis. This
is the ingredient the transverse-field Ising layer
(`Qhl/Register/TFIM.lean`) drives along a product state: every generic qubit
fact lives here, none in an example.
-/

namespace Qhl

/-! ## Coordinates of the diagonal kets -/

/-- Both coordinates of `∣+⟩` are `1/√2`. -/
theorem qplus_apply (b : Bool) : qplus b = (Real.sqrt 2 : ℂ)⁻¹ := by
  cases b <;> simp [qplus]

/-- The coordinates of `∣-⟩` are `1/√2` and `-1/√2`. -/
theorem qminus_apply (b : Bool) :
    qminus b = if b then -(Real.sqrt 2 : ℂ)⁻¹ else (Real.sqrt 2 : ℂ)⁻¹ := by
  cases b <;> simp [qminus]

/-! ## The unit-modulus exponential, split into its coordinates -/

/-- `e^{-ix} = cos x - i sin x`, in the form the `rxMat` entries take. -/
theorem exp_neg_ofReal_mul_I (x : ℝ) :
    Complex.exp ((-x : ℝ) * Complex.I)
      = (Real.cos x : ℂ) + -Complex.I * (Real.sin x : ℂ) := by
  rw [Complex.ofReal_neg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- `e^{ix} = cos x + i sin x`, in the form the `rxMat` entries take. -/
theorem exp_ofReal_mul_I (x : ℝ) :
    Complex.exp ((x : ℝ) * Complex.I)
      = (Real.cos x : ℂ) + Complex.I * (Real.sin x : ℂ) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-! ## The `Rx` action on the `±` basis -/

/-- `∣+⟩` is the `+1`-eigenvector of `X`, so `Rx θ = e^{-i(θ/2)X}` scales it by
`e^{-iθ/2}`. -/
theorem Rx_qplus (θ : ℝ) :
    (Rx θ : 𝕢 →ₗ[ℂ] 𝕢) qplus
      = Complex.exp ((-(θ / 2) : ℝ) * Complex.I) • qplus := by
  ext b
  rw [show ((Rx θ : 𝕢 →ₗ[ℂ] 𝕢)) = matOp (rxMat θ) from rfl, matOp_apply,
    Fintype.sum_bool, PiLp.smul_apply, qplus_apply, qplus_apply, qplus_apply,
    smul_eq_mul, exp_neg_ofReal_mul_I]
  cases b <;> · simp [rxMat]; ring

/-- `∣-⟩` is the `-1`-eigenvector of `X`, so `Rx θ = e^{-i(θ/2)X}` scales it by
`e^{+iθ/2}`. -/
theorem Rx_qminus (θ : ℝ) :
    (Rx θ : 𝕢 →ₗ[ℂ] 𝕢) qminus
      = Complex.exp ((θ / 2 : ℝ) * Complex.I) • qminus := by
  ext b
  rw [show ((Rx θ : 𝕢 →ₗ[ℂ] 𝕢)) = matOp (rxMat θ) from rfl, matOp_apply,
    Fintype.sum_bool, PiLp.smul_apply, qminus_apply, qminus_apply, qminus_apply,
    smul_eq_mul, exp_ofReal_mul_I]
  cases b <;> · simp [rxMat]; ring

/-! ## The `±` basis family and the uniform eigenvalue law -/

/-- The `±`-basis family: `pmKet false = ∣+⟩`, `pmKet true = ∣-⟩` — the
`X`-eigenbasis, indexed the same way the computational basis indexes the
`Z`-eigenbasis. -/
noncomputable def pmKet (b : Bool) : 𝕢 := if b then qminus else qplus

@[simp] theorem pmKet_false : pmKet false = qplus := rfl

@[simp] theorem pmKet_true : pmKet true = qminus := rfl

/-- Each `∣±⟩` is a unit vector. -/
@[simp] theorem norm_pmKet (b : Bool) : ‖pmKet b‖ = 1 := by
  cases b <;> simp [pmKet]

/-- **The `Rx` eigenvalue law on the `±` basis**:
`Rx θ (pmKet b) = e^{-i(θ/2)·z(b)} (pmKet b)` — the `±`-basis analogue of
`Rz_single`, with the same eigenvalue function `zsign`. -/
theorem Rx_pmKet (θ : ℝ) (b : Bool) :
    (Rx θ : 𝕢 →ₗ[ℂ] 𝕢) (pmKet b)
      = Complex.exp ((-(θ / 2 * zsign b) : ℝ) * Complex.I) • pmKet b := by
  cases b
  · rw [pmKet_false, zsign_false, mul_one, Rx_qplus]
  · rw [pmKet_true, zsign_true, Rx_qminus,
      show (-(θ / 2 * (-1 : ℝ)) : ℝ) = θ / 2 by ring]

end Qhl
