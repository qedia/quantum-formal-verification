import Qhl.Gate.Qubit
import Qhl.Gate.Phase

/-!
# The two-qubit `ZZ`-rotation gate `Rzz`

The gate atom of the Ising-coupling term: `Rzz θ = e^{-i(θ/2) Z⊗Z}` on
`EuclideanSpace ℂ (Bool × Bool)`, a diagonal gate in the computational basis,

```
Rzz θ ∣y₁y₂⟩ = e^{-i(θ/2)·z(y₁)z(y₂)} ∣y₁y₂⟩,
```

where `z : Bool → ℝ` is the `Z`-eigenvalue `z(false) = 1`, `z(true) = -1` —
so the phase is `e^{-iθ/2}` when the two bits agree and `e^{+iθ/2}` when they
differ, consistent with the half-angle convention of
`Rz θ = diag(e^{-iθ/2}, e^{iθ/2}) = e^{-i(θ/2)Z}` (`Qhl/Gate/Qubit.lean`).

Built by the cheapest G-1 construction available, the unit-modulus diagonal
`diagOp` (like `Z`, `S`, `CZ`, `phase`), so unitarity is free. The basis
action `Rzz_single` and its product-vector form `Rzz_vpair` (the shape the
two-cell register bridge `regLift_pairGate_prodV` consumes) are proved here;
`zsign` and the `zsign`-form of the `Rz` basis action are shared with the
diagonal Ising layer `Qhl/Register/IsingDiag.lean`.
-/

namespace Qhl

/-- The `Z`-eigenvalue of a computational basis value: `z(false) = 1`,
`z(true) = -1`, so that `Z ∣b⟩ = z(b) ∣b⟩` and
`Rz θ ∣b⟩ = e^{-i(θ/2)·z(b)} ∣b⟩` in the convention of `Qhl/Gate/Qubit.lean`.

More precisely, `zsign` is the basis-neutral sign `(-1)^b` of a bit `b`, and
the library uses this one function for both eigenvalue readings: on
computational bits it is the `Z`-eigenvalue (`Z ∣b⟩ = z(b) ∣b⟩`; the paper
writes `z(·)`), while on bits labelling the `±` basis (as in
`pmState`/`aPart_pmState`/`AOp_pmState`, `Qhl/Register/TFIM.lean`) it is the
`X`-eigenvalue (`X ∣±_b⟩ = (-1)^b ∣±_b⟩`; the paper writes `x(·)` there). -/
def zsign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem zsign_false : zsign false = 1 := rfl

@[simp] theorem zsign_true : zsign true = -1 := rfl

/-- `EuclideanSpace.single` is homogeneous in its value. -/
theorem single_eq_smul_single {α : Type*} [Fintype α] [DecidableEq α] (i : α) (c : ℂ) :
    EuclideanSpace.single i c = c • EuclideanSpace.single i (1 : ℂ) := by
  ext j
  by_cases h : j = i <;>
    simp [PiLp.single_apply, PiLp.smul_apply, smul_eq_mul, h]

/-- The `Rz` basis action in `zsign` form: `Rz θ ∣b⟩ = e^{-i(θ/2)·z(b)} ∣b⟩`
(the diagonal entries of `Rz θ = diag(e^{-iθ/2}, e^{iθ/2})`, read through the
`Z`-eigenvalue). -/
theorem Rz_single (θ : ℝ) (b : Bool) (c : ℂ) :
    (Rz θ : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single b c)
      = Complex.exp ((-(θ / 2 * zsign b) : ℝ) * Complex.I) •
          EuclideanSpace.single b c := by
  rw [Rz, diagOp_single, single_eq_smul_single b _, single_eq_smul_single b c, smul_smul]
  congr 2
  cases b <;> norm_num [zsign]

/-- The two-qubit `ZZ`-rotation `Rzz θ = e^{-i(θ/2) Z⊗Z}`: the diagonal gate
`∣y₁y₂⟩ ↦ e^{-i(θ/2)·z(y₁)z(y₂)} ∣y₁y₂⟩` — phase `e^{-iθ/2}` when the two bits
agree, `e^{+iθ/2}` when they differ. -/
noncomputable def Rzz (θ : ℝ) : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)) :=
  diagOp (fun p => Complex.exp ((-(θ / 2 * (zsign p.1 * zsign p.2)) : ℝ) * Complex.I))
    (fun _ => Complex.norm_exp_ofReal_mul_I _)

/-- The defining basis action of `Rzz`. -/
theorem Rzz_single (θ : ℝ) (p : Bool × Bool) (c : ℂ) :
    (Rzz θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (EuclideanSpace.single p c)
      = Complex.exp ((-(θ / 2 * (zsign p.1 * zsign p.2)) : ℝ) * Complex.I) •
          EuclideanSpace.single p c := by
  rw [Rzz, diagOp_single, single_eq_smul_single p _, single_eq_smul_single p c, smul_smul]

/-- The basis action of `Rzz` on a product of basis kets, in the two-factor
`vpair` form the pair-register bridge `regLift_pairGate_prodV`
(`Qhl/Logic/Frame.lean`) consumes: the phase is carried on the first factor. -/
theorem Rzz_vpair (θ : ℝ) (y₁ y₂ : Bool) :
    (Rzz θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair (EuclideanSpace.single y₁ (1 : ℂ)) (EuclideanSpace.single y₂ (1 : ℂ)))
      = vpair
          (Complex.exp ((-(θ / 2 * (zsign y₁ * zsign y₂)) : ℝ) * Complex.I) •
            EuclideanSpace.single y₁ (1 : ℂ))
          (EuclideanSpace.single y₂ (1 : ℂ)) := by
  rw [vpair_single, one_mul, Rzz_single, vpair_smul_left, vpair_single, one_mul]

end Qhl
