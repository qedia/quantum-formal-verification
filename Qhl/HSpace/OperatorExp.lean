import Qhl.HSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The operator exponential on a labelled space

The exponential `expOp A = e^A` of a labelled endomorphism `A : EndM D S` —
the operator a Hamiltonian `H` generates as its evolution `e^{-iφH}`.  The
labelled space `HS D S` is finite-dimensional, so every endomorphism is
continuous: `expOp` is mathlib's Banach-algebra exponential `NormedSpace.exp`
on the continuous endomorphisms, transported along
`LinearMap.toContinuousLinearMap` (the inverse transport is the coercion back
to a plain linear map).

* `expOp A` — the exponential series `Σₖ Aᵏ/k!`, summed in the operator norm;
* `expOp_eigenvector` — **the evaluation rule**: on an eigenvector `A v = c • v`
  the exponential is the scalar exponential of the eigenvalue,
  `expOp A v = e^c • v`.  Evaluation at `v` is a continuous linear map, so it
  passes through the series term by term, where `Aᵏ v = cᵏ • v`; the resulting
  scalar series is the series of `Complex.exp c`.

A diagonalizable operator is determined by `expOp_eigenvector` on an
eigenbasis: this is how the rotation-gate layers of a Trotter slice are
identified with the exponentials `e^{-iφH}` of their Hamiltonians
(`Qhl/Register/TFIM.lean`).

**Ownership test.**  Generic in the labels `L`, the cell family `D` and the
label set `S`; no program, no gate and no example fixture is named.
-/

namespace Qhl

open scoped Nat

variable {L : Type*} [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S : Finset L}

/-- **The operator exponential** `e^A` of a labelled endomorphism: the
Banach-algebra exponential `NormedSpace.exp` of `A` viewed as a continuous
endomorphism of the finite-dimensional space `HS D S`, viewed back as a plain
endomorphism. -/
noncomputable def expOp (A : EndM D S) : EndM D S :=
  ((NormedSpace.exp (LinearMap.toContinuousLinearMap A) :
      HS D S →L[ℂ] HS D S) : HS D S →ₗ[ℂ] HS D S)

omit [∀ i, DecidableEq (D i)] in
/-- Powers of an endomorphism fix its eigenvectors up to the power of the
eigenvalue: `A v = c • v → Aᵏ v = cᵏ • v`. -/
theorem pow_toContinuousLinearMap_eigenvector {A : EndM D S} {v : HS D S} {c : ℂ}
    (h : A v = c • v) :
    ∀ k : ℕ, ((LinearMap.toContinuousLinearMap A) ^ k) v = c ^ k • v := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_apply_eq_comp,
        show (LinearMap.toContinuousLinearMap A) v = A v from rfl, h, map_smul, ih,
        smul_smul, pow_succ, mul_comm]

omit [∀ i, DecidableEq (D i)] in
/-- **The evaluation rule of the operator exponential**: on an eigenvector of
`A` with eigenvalue `c`, the operator exponential is the scalar exponential of
the eigenvalue — `A v = c • v → e^A v = e^c • v`.  Evaluation at `v` is a
continuous linear map, so the exponential series passes through it term by
term (`Aᵏ v = cᵏ • v`), and the resulting scalar series sums to
`Complex.exp c`. -/
theorem expOp_eigenvector {A : EndM D S} {v : HS D S} {c : ℂ}
    (h : A v = c • v) : expOp A v = Complex.exp c • v := by
  have h1 : HasSum (fun k : ℕ => (k !⁻¹ : ℂ) • (LinearMap.toContinuousLinearMap A) ^ k)
      (NormedSpace.exp (LinearMap.toContinuousLinearMap A)) :=
    NormedSpace.exp_series_hasSum_exp' _
  have h2 := (ContinuousLinearMap.apply ℂ (HS D S) v).hasSum h1
  simp only [ContinuousLinearMap.apply_apply, smul_apply,
    pow_toContinuousLinearMap_eigenvector h] at h2
  have h3 : HasSum (fun k : ℕ => (k !⁻¹ : ℂ) • c ^ k • v) (NormedSpace.exp c • v) := by
    have h4 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const v
    simpa only [smul_assoc] using h4
  have h5 : expOp A v
      = (NormedSpace.exp (LinearMap.toContinuousLinearMap A) : HS D S →L[ℂ] HS D S) v := rfl
  rw [h5, h2.unique h3, Complex.exp_eq_exp_ℂ]

end Qhl
