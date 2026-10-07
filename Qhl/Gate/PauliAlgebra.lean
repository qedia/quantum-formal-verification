import Qhl.Gate.Qubit

/-!
# The single-qubit Pauli algebra

The one-qubit gates `X`, `Y`, `Z` already exist in `Qhl/Gate/Qubit.lean`
(a basis permutation, a matrix operator, a diagonal operator).  This file adds
the *algebra* they satisfy, at the level of linear maps on the qubit space `𝕢`:

* uniform basis actions `X_single`/`Y_single`/`Z_single` — each Pauli sends the
  computational basis ket `∣b⟩` to a unit scalar times a basis ket
  (`X∣b⟩ = ∣¬b⟩`, `Y∣b⟩ = i(-1)^b ∣¬b⟩`, `Z∣b⟩ = (-1)^b ∣b⟩`);
* the multiplication table `X∘Y = iZ`, `Y∘Z = iX`, `Z∘X = iY` and the three
  reversed products with the opposite sign;
* the involutions `X∘X = Y∘Y = Z∘Z = 1`;
* the pairwise anticommutation relations `XY + YX = 0` etc.

Everything is proved by the two-point extensionality `qubitLM_ext` (a linear
map on `𝕢` is determined by its values on `∣0⟩`, `∣1⟩`) plus the basis actions.
-/

namespace Qhl

open scoped ComplexInnerProductSpace

/-! ## Extensionality on the qubit space -/

/-- A linear map on the qubit space is determined by its values on the two
computational basis kets. -/
theorem qubitLM_ext {A B : 𝕢 →ₗ[ℂ] 𝕢}
    (h : ∀ b : Bool, A (EuclideanSpace.single b 1) = B (EuclideanSpace.single b 1)) :
    A = B := by
  refine LinearMap.ext fun v => ?_
  have hv : v = v false • EuclideanSpace.single false (1 : ℂ)
      + v true • EuclideanSpace.single true (1 : ℂ) := by
    ext b
    cases b <;>
      simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hv]
  simp only [map_add, map_smul, h false, h true]

/-! ## Uniform basis actions -/

/-- `X ∣b⟩ = ∣¬b⟩`. -/
theorem X_single (b : Bool) :
    (X : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single b 1) = EuclideanSpace.single (!b) 1 :=
  permOp_single _ _ _

/-- `Z ∣b⟩ = (-1)^b • ∣b⟩`. -/
theorem Z_single (b : Bool) :
    (Z : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single b 1)
      = (if b then (-1 : ℂ) else 1) • EuclideanSpace.single b 1 := by
  rw [Z, diagOp_single]
  ext i
  cases b <;> cases i <;> simp [PiLp.single_apply, PiLp.smul_apply, smul_eq_mul]

/-- `Y ∣b⟩ = i·(-1)^b • ∣¬b⟩`. -/
theorem Y_single (b : Bool) :
    (Y : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single b 1)
      = (if b then -Complex.I else Complex.I) • EuclideanSpace.single (!b) 1 := by
  ext i
  rw [Y, coe_unitaryOfMat, matOp_single]
  cases b <;> cases i <;>
    simp [yMat, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]

/-! ## Involutions -/

theorem X_comp_X : (X : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (X : 𝕢 →ₗ[ℂ] 𝕢) = 1 :=
  qubitLM_ext fun b => by
    cases b <;>
      simp [LinearMap.comp_apply, X_single, Module.End.one_apply]

theorem Y_comp_Y : (Y : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (Y : 𝕢 →ₗ[ℂ] 𝕢) = 1 :=
  qubitLM_ext fun b => by
    cases b <;>
      simp [LinearMap.comp_apply, Y_single, Module.End.one_apply, map_smul,
        smul_smul, Complex.I_mul_I]

theorem Z_comp_Z : (Z : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (Z : 𝕢 →ₗ[ℂ] 𝕢) = 1 :=
  qubitLM_ext fun b => by
    cases b <;>
      simp [LinearMap.comp_apply, Z_single, Module.End.one_apply, map_smul, smul_smul]

/-! ## The multiplication table -/

theorem X_comp_Y :
    (X : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (Y : 𝕢 →ₗ[ℂ] 𝕢) = Complex.I • (Z : 𝕢 →ₗ[ℂ] 𝕢) :=
  qubitLM_ext fun b => by
    cases b <;>
      simp [LinearMap.comp_apply, X_single, Y_single, Z_single, LinearMap.smul_apply,
        map_smul, smul_smul]

theorem Y_comp_X :
    (Y : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (X : 𝕢 →ₗ[ℂ] 𝕢) = (-Complex.I) • (Z : 𝕢 →ₗ[ℂ] 𝕢) :=
  qubitLM_ext fun b => by
    cases b <;>
      simp [LinearMap.comp_apply, X_single, Y_single, Z_single, LinearMap.smul_apply,
        map_smul, smul_smul]

theorem Y_comp_Z :
    (Y : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (Z : 𝕢 →ₗ[ℂ] 𝕢) = Complex.I • (X : 𝕢 →ₗ[ℂ] 𝕢) :=
  qubitLM_ext fun b => by
    cases b <;>
      simp [LinearMap.comp_apply, X_single, Y_single, Z_single, LinearMap.smul_apply,
        map_smul, smul_smul]

theorem Z_comp_Y :
    (Z : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (Y : 𝕢 →ₗ[ℂ] 𝕢) = (-Complex.I) • (X : 𝕢 →ₗ[ℂ] 𝕢) :=
  qubitLM_ext fun b => by
    cases b <;>
      simp [LinearMap.comp_apply, X_single, Y_single, Z_single, LinearMap.smul_apply,
        map_smul, smul_smul]

theorem Z_comp_X :
    (Z : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (X : 𝕢 →ₗ[ℂ] 𝕢) = Complex.I • (Y : 𝕢 →ₗ[ℂ] 𝕢) :=
  qubitLM_ext fun b => by
    cases b <;>
      simp [LinearMap.comp_apply, X_single, Y_single, Z_single, LinearMap.smul_apply,
        map_smul, smul_smul, Complex.I_mul_I]

theorem X_comp_Z :
    (X : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (Z : 𝕢 →ₗ[ℂ] 𝕢) = (-Complex.I) • (Y : 𝕢 →ₗ[ℂ] 𝕢) :=
  qubitLM_ext fun b => by
    cases b <;>
      simp [LinearMap.comp_apply, X_single, Y_single, Z_single, LinearMap.smul_apply,
        map_smul, smul_smul, Complex.I_mul_I]

/-! ## Anticommutation -/

theorem X_anticomm_Y :
    (X : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (Y : 𝕢 →ₗ[ℂ] 𝕢) + (Y : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (X : 𝕢 →ₗ[ℂ] 𝕢) = 0 := by
  rw [X_comp_Y, Y_comp_X, neg_smul, add_neg_cancel]

theorem Y_anticomm_Z :
    (Y : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (Z : 𝕢 →ₗ[ℂ] 𝕢) + (Z : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (Y : 𝕢 →ₗ[ℂ] 𝕢) = 0 := by
  rw [Y_comp_Z, Z_comp_Y, neg_smul, add_neg_cancel]

theorem Z_anticomm_X :
    (Z : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (X : 𝕢 →ₗ[ℂ] 𝕢) + (X : 𝕢 →ₗ[ℂ] 𝕢) ∘ₗ (Z : 𝕢 →ₗ[ℂ] 𝕢) = 0 := by
  rw [Z_comp_X, X_comp_Z, neg_smul, add_neg_cancel]

end Qhl
