import Qhl.Gate.Qubit
import Qhl.Gate.Phase
import Qhl.Gate.PauliAlgebra

/-!
# The Givens (partial-swap) rotation and the sign gate

The two constant-arity gate atoms an LCU state-preparation chain needs:

* `givens θ` — the two-qubit rotation in the `{∣10⟩, ∣01⟩}` block:
  `∣10⟩ ↦ cos θ ∣10⟩ + sin θ ∣01⟩`, `∣01⟩ ↦ -sin θ ∣10⟩ + cos θ ∣01⟩`, the
  computational states `∣00⟩` and `∣11⟩` fixed.  Chained along a line of
  ancilla cells it moves amplitude down a one-hot register — the standard
  W-state-style preparation step, with the angle a run-time parameter (the
  paper's parameterized-gate feature).  `givens_mul_neg` is the inverse law
  `givens θ · givens (-θ) = 1` that the un-preparation chain runs on.
* `sgnGate r` — the one-qubit diagonal `diag(1, sign r)`: the controlled
  `±1` phase that plants the sign of the coefficient `r` on a set ancilla
  bit (`Z` exactly when `r < 0`, the identity otherwise).

Both come with their computational basis actions in the `vpair`/`qbit` form
the embedding collapses (`Qhl/Logic/AncillaEmbed.lean`) consume.
-/

namespace Qhl

open scoped Matrix

/-! ## §1. The Givens rotation -/

/-- The matrix of the Givens rotation in the `{∣10⟩, ∣01⟩}` block. -/
noncomputable def givensMat (θ : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q =>
    match p, q with
    | (false, false), (false, false) => 1
    | (true, true), (true, true) => 1
    | (true, false), (true, false) => (Real.cos θ : ℂ)
    | (false, true), (true, false) => (Real.sin θ : ℂ)
    | (true, false), (false, true) => -(Real.sin θ : ℂ)
    | (false, true), (false, true) => (Real.cos θ : ℂ)
    | _, _ => 0

/-- **The Givens rotation gate.** -/
noncomputable def givens (θ : ℝ) : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)) :=
  unitaryOfMat (givensMat θ) <| by
    ext p q
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [givensMat, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Fintype.sum_bool,
        -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
      ring_nf <;> norm_cast <;> linarith [Real.sin_sq_add_cos_sq θ]

/-- The product of the two basis kets of a two-qubit cell pair. -/
theorem vpair_qbit (a b : Bool) :
    vpair (qbit a) (qbit b) = EuclideanSpace.single (a, b) (1 : ℂ) := by
  rw [qbit, qbit, vpair_single, mul_one]

/-- `∣00⟩` is fixed. -/
theorem givens_vpair_00 (θ : ℝ) :
    (givens θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair (qbit false) (qbit false)) = vpair (qbit false) (qbit false) := by
  rw [vpair_qbit]
  ext p
  obtain ⟨u, v⟩ := p
  rw [show ((givens θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ]
      EuclideanSpace ℂ (Bool × Bool))) = matOp (givensMat θ) from rfl, matOp_single]
  cases u <;> cases v <;> simp [givensMat]

/-- `∣11⟩` is fixed. -/
theorem givens_vpair_11 (θ : ℝ) :
    (givens θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair (qbit true) (qbit true)) = vpair (qbit true) (qbit true) := by
  rw [vpair_qbit]
  ext p
  obtain ⟨u, v⟩ := p
  rw [show ((givens θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ]
      EuclideanSpace ℂ (Bool × Bool))) = matOp (givensMat θ) from rfl, matOp_single]
  cases u <;> cases v <;> simp [givensMat]

/-- `∣10⟩ ↦ cos θ ∣10⟩ + sin θ ∣01⟩` — the amplitude-moving step. -/
theorem givens_vpair_10 (θ : ℝ) :
    (givens θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair (qbit true) (qbit false))
      = (Real.cos θ : ℂ) • vpair (qbit true) (qbit false)
        + (Real.sin θ : ℂ) • vpair (qbit false) (qbit true) := by
  rw [vpair_qbit, vpair_qbit]
  ext p
  obtain ⟨u, v⟩ := p
  rw [show ((givens θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ]
      EuclideanSpace ℂ (Bool × Bool))) = matOp (givensMat θ) from rfl, matOp_single]
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  cases u <;> cases v <;> simp [givensMat]

/-- `∣01⟩ ↦ -sin θ ∣10⟩ + cos θ ∣01⟩`. -/
theorem givens_vpair_01 (θ : ℝ) :
    (givens θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair (qbit false) (qbit true))
      = (-(Real.sin θ) : ℂ) • vpair (qbit true) (qbit false)
        + (Real.cos θ : ℂ) • vpair (qbit false) (qbit true) := by
  rw [vpair_qbit, vpair_qbit]
  ext p
  obtain ⟨u, v⟩ := p
  rw [show ((givens θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ]
      EuclideanSpace ℂ (Bool × Bool))) = matOp (givensMat θ) from rfl, matOp_single]
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  cases u <;> cases v <;> simp [givensMat]

/-- The inverse law of the preparation chain: `givens θ · givens (-θ) = 1`. -/
theorem givens_mul_neg (θ : ℝ) : givens θ * givens (-θ) = 1 := by
  refine Subtype.ext ?_
  rw [UnitaryOp.coe_mul,
    show ((givens θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool)))
      = matOp (givensMat θ) from rfl,
    show ((givens (-θ) : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool)))
      = matOp (givensMat (-θ)) from rfl,
    ← matOp_mul]
  rw [show givensMat θ * givensMat (-θ) = 1 from ?_]
  · rw [matOp_one]
    rfl
  · ext p q
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    cases a <;> cases b <;> cases c <;> cases d <;>
      simp [givensMat, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
        Matrix.one_apply, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
      ring_nf <;> norm_cast <;> linarith [Real.sin_sq_add_cos_sq θ]

/-- `givens (-θ) · givens θ = 1`. -/
theorem givens_neg_mul (θ : ℝ) : givens (-θ) * givens θ = 1 := by
  have h := givens_mul_neg (-θ)
  rwa [neg_neg] at h

/-! ## §2. The sign gate -/

/-- The one-qubit diagonal gate `diag(1, sign r)`: `Z` exactly when `r < 0`,
the identity otherwise. -/
noncomputable def sgnGate (r : ℝ) : UnitaryOp 𝕢 :=
  diagOp (fun b => if b then (if r < 0 then -1 else 1) else 1) <| by
    intro b
    cases b <;> split_ifs <;> simp

/-- The sign gate's basis action: the set bit acquires the sign of `r`. -/
theorem sgnGate_single (r : ℝ) (b : Bool) :
    (sgnGate r : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single b 1)
      = (if b then (if r < 0 then (-1 : ℂ) else 1) else 1) •
          EuclideanSpace.single b 1 := by
  rw [sgnGate, diagOp_single]
  ext c
  simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  rcases eq_or_ne c b with rfl | h
  · simp
  · simp [h]

/-- The sign gate is an involution. -/
theorem sgnGate_mul_self (r : ℝ) : sgnGate r * sgnGate r = 1 := by
  refine Subtype.ext ?_
  rw [UnitaryOp.coe_mul, UnitaryOp.coe_one]
  refine qubitLM_ext fun b => ?_
  rw [LinearMap.comp_apply, Module.End.one_apply, sgnGate_single, map_smul,
    sgnGate_single, smul_smul]
  cases b <;> split_ifs <;> norm_num

end Qhl
