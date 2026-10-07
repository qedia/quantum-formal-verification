import Qhl.Gate.Unitary

/-!
# G-2/G-3: the qubit, its gates, and the two-qubit combinators

Subgoals G-2 and G-3 of spec 06.

* **G-2** the qubit space `𝕢 = EuclideanSpace ℂ Bool`, the kets
  `q0 q1 qplus qminus`, and the standard one-qubit gates `X Y Z S H`,
  `phase θ`, `Rx θ`, `Ry θ`, `Rz θ`, each a bundled `UnitaryOp 𝕢`.
* **G-3** the two-qubit gates `CNOT`, `CZ`, `SWAP` on
  `EuclideanSpace ℂ (Bool × Bool)` and the controlled-gate combinator
  `control U`, the block-diagonal `1 ⊕ U`.

Every gate is built by the cheapest G-1 construction available: a basis
permutation (`permOp`), a unit-modulus diagonal (`diagOp`), or an explicit
matrix (`unitaryOfMat`). CoqQ counterpart: `qtype.v`.
-/

namespace Qhl

open scoped Matrix

/-! ## Action of the G-1 constructions on basis kets -/

section Single

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A matrix operator sends `∣j⟩` to the `j`-th column. -/
theorem matOp_single (M : Matrix α α ℂ) (j : α) (c : ℂ) (i : α) :
    matOp M (EuclideanSpace.single j c) i = M i j * c := by
  rw [matOp_apply]; simp

/-- A permutation gate permutes the basis kets. -/
theorem permOp_single (e : α ≃ α) (i : α) (c : ℂ) :
    (permOp e : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α) (EuclideanSpace.single i c)
      = EuclideanSpace.single (e i) c := euclCongr_single e i c

/-- A diagonal gate scales each basis ket. -/
theorem diagOp_single (d : α → ℂ) (hd : ∀ a, ‖d a‖ = 1) (i : α) (c : ℂ) :
    (diagOp d hd : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α) (EuclideanSpace.single i c)
      = EuclideanSpace.single i (d i * c) := by
  ext j
  rw [show ((diagOp d hd : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α))
      = matOp (Matrix.diagonal d) from rfl, matOp_single]
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [h]

end Single

/-! ## G-2: the qubit and its kets -/

/-- The one-qubit state space. -/
abbrev 𝕢 : Type := EuclideanSpace ℂ Bool

/-- The computational basis ket `∣0⟩`. -/
noncomputable def q0 : 𝕢 := EuclideanSpace.single false 1

/-- The computational basis ket `∣1⟩`. -/
noncomputable def q1 : 𝕢 := EuclideanSpace.single true 1

/-- The ket `∣+⟩ = (∣0⟩ + ∣1⟩)/√2`. -/
noncomputable def qplus : 𝕢 := (Real.sqrt 2 : ℂ)⁻¹ • (q0 + q1)

/-- The ket `∣-⟩ = (∣0⟩ - ∣1⟩)/√2`. -/
noncomputable def qminus : 𝕢 := (Real.sqrt 2 : ℂ)⁻¹ • (q0 - q1)

/-- `1/√2` squares to `1/2`. -/
theorem inv_sqrt_two_mul_self : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 2⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- `1/√2` is real, hence fixed by conjugation. -/
theorem star_inv_sqrt_two : star ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
  rw [star_inv₀, RCLike.star_def, Complex.conj_ofReal]

@[simp]
theorem q0_apply (b : Bool) : q0 b = if b = false then 1 else 0 := by simp [q0]

@[simp]
theorem q1_apply (b : Bool) : q1 b = if b = true then 1 else 0 := by simp [q1]

@[simp]
theorem norm_q0 : ‖q0‖ = 1 := by simp [q0]

@[simp]
theorem norm_q1 : ‖q1‖ = 1 := by simp [q1]

@[simp]
theorem norm_qplus : ‖qplus‖ = 1 := by rw [EuclideanSpace.norm_eq]; norm_num [qplus]

@[simp]
theorem norm_qminus : ‖qminus‖ = 1 := by rw [EuclideanSpace.norm_eq]; norm_num [qminus]

/-! ## G-2: the one-qubit gates -/

/-- The Pauli `X` (bit flip) gate, the basis permutation `b ↦ ¬b`. -/
noncomputable def X : UnitaryOp 𝕢 := permOp ⟨not, not, Bool.not_not, Bool.not_not⟩

/-- The Pauli `Z` (phase flip) gate. -/
noncomputable def Z : UnitaryOp 𝕢 :=
  diagOp (fun b => if b then -1 else 1) (by intro b; cases b <;> simp)

/-- The phase gate `S = diag(1, i)`. -/
noncomputable def S : UnitaryOp 𝕢 :=
  diagOp (fun b => if b then Complex.I else 1) (by intro b; cases b <;> simp)

/-- The parameterised phase gate `diag(1, e^{iθ})`. -/
noncomputable def phase (θ : ℝ) : UnitaryOp 𝕢 :=
  diagOp (fun b => if b then Complex.exp (θ * Complex.I) else 1)
    (by intro b; cases b <;> simp [Complex.norm_exp_ofReal_mul_I])

/-- The `z`-rotation `diag(e^{-iθ/2}, e^{iθ/2})`. -/
noncomputable def Rz (θ : ℝ) : UnitaryOp 𝕢 :=
  diagOp (fun b => Complex.exp (((if b then θ / 2 else -(θ / 2) : ℝ)) * Complex.I))
    (fun _ => Complex.norm_exp_ofReal_mul_I _)

/-! ### Diagonal-gate coordinates and the rotation-addition law

`Rz` is a diagonal gate, so its action on a vector is coordinatewise
multiplication; the diagonal entries are unit-modulus exponentials, and their
product rule `e^{-iaZ/2} e^{-ibZ/2} = e^{-i(a+b)Z/2}` is the group law of the
`z`-rotations. The generic coordinate lemma `diagOp_apply` and the two `Rz`
corollaries below are program-agnostic gate algebra; they belong to the gate
library, not to any example. -/

section DiagLemmas

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A diagonal gate acts coordinatewise: `(diagOp d) v i = d i * v i`. -/
theorem diagOp_apply (d : α → ℂ) (hd : ∀ a, ‖d a‖ = 1) (v : EuclideanSpace ℂ α) (i : α) :
    (diagOp d hd : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α) v i = d i * v i := by
  rw [show ((diagOp d hd : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α))
      = matOp (Matrix.diagonal d) from rfl, matOp_apply]
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

end DiagLemmas

/-- `Rz 0` is the identity: the zero rotation leaves every state fixed. -/
@[simp]
theorem Rz_zero_apply (v : 𝕢) : (Rz 0 : 𝕢 →ₗ[ℂ] 𝕢) v = v := by
  ext i
  simp only [Rz, diagOp_apply]
  cases i <;> simp

/-- **The rotation-addition law** `Rz a ∘ Rz b = Rz (a + b)`, pointwise:
`e^{-iaZ/2} e^{-ibZ/2} = e^{-i(a+b)Z/2}`. One Trotter step `Rz b` composed with
the small rotation `Rz a` is the rotation by the summed angle — the exactness of
the product formula for `H = Z`. -/
theorem Rz_Rz_apply (a b : ℝ) (v : 𝕢) :
    (Rz a : 𝕢 →ₗ[ℂ] 𝕢) ((Rz b : 𝕢 →ₗ[ℂ] 𝕢) v) = (Rz (a + b) : 𝕢 →ₗ[ℂ] 𝕢) v := by
  ext i
  simp only [Rz, diagOp_apply]
  rw [← mul_assoc, ← Complex.exp_add]
  have h : (↑(if i then a / 2 else -(a / 2)) : ℂ) * Complex.I
        + ↑(if i then b / 2 else -(b / 2)) * Complex.I
      = ↑(if i then (a + b) / 2 else -((a + b) / 2)) * Complex.I := by
    cases i <;> simp only [if_true, if_false, Bool.false_eq_true] <;> push_cast <;> ring
  rw [h]

/-- The matrix of the Pauli `Y` gate. -/
noncomputable def yMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a = b then 0 else if b then -Complex.I else Complex.I

/-- The Pauli `Y` gate. -/
noncomputable def Y : UnitaryOp 𝕢 :=
  unitaryOfMat yMat <| by
    ext i j
    cases i <;> cases j <;>
      simp [yMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.I_mul_I]

/-- The matrix of the Hadamard gate. -/
noncomputable def hMat : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => (Real.sqrt 2 : ℂ)⁻¹ * (if a && b then -1 else 1)

/-- The Hadamard gate. -/
noncomputable def H : UnitaryOp 𝕢 :=
  unitaryOfMat hMat <| by
    ext i j
    cases i <;> cases j <;>
      norm_num [hMat, Matrix.mul_apply, Matrix.conjTranspose_apply, inv_sqrt_two_mul_self]

/-- The matrix of the `x`-rotation gate. -/
noncomputable def rxMat (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    if a = b then (Real.cos (θ / 2) : ℂ) else -Complex.I * (Real.sin (θ / 2) : ℂ)

/-- The `x`-rotation `exp(-iθX/2)`. -/
noncomputable def Rx (θ : ℝ) : UnitaryOp 𝕢 :=
  unitaryOfMat (rxMat θ) <| by
    ext i j
    cases i <;> cases j <;>
      simp [rxMat, Matrix.mul_apply, Matrix.conjTranspose_apply,
        -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
      ring_nf <;> simp only [Complex.I_sq] <;> ring_nf <;> norm_cast <;>
      linarith [Real.sin_sq_add_cos_sq (θ * (1 / 2))]

/-- The matrix of the `y`-rotation gate. -/
noncomputable def ryMat (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b =>
    if a = b then (Real.cos (θ / 2) : ℂ)
    else if b then -(Real.sin (θ / 2) : ℂ) else (Real.sin (θ / 2) : ℂ)

/-- The `y`-rotation `exp(-iθY/2)`. -/
noncomputable def Ry (θ : ℝ) : UnitaryOp 𝕢 :=
  unitaryOfMat (ryMat θ) <| by
    ext i j
    cases i <;> cases j <;>
      simp [ryMat, Matrix.mul_apply, Matrix.conjTranspose_apply,
        -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
      ring_nf <;> norm_cast <;> linarith [Real.sin_sq_add_cos_sq (θ * (1 / 2))]

/-! ### Action of the one-qubit gates on the basis kets -/

@[simp]
theorem X_q0 : (X : 𝕢 →ₗ[ℂ] 𝕢) q0 = q1 := permOp_single _ _ _

@[simp]
theorem X_q1 : (X : 𝕢 →ₗ[ℂ] 𝕢) q1 = q0 := permOp_single _ _ _

@[simp]
theorem Z_q0 : (Z : 𝕢 →ₗ[ℂ] 𝕢) q0 = q0 := by
  rw [Z, q0, diagOp_single]; norm_num

@[simp]
theorem Z_q1 : (Z : 𝕢 →ₗ[ℂ] 𝕢) q1 = -q1 := by
  rw [Z, q1, diagOp_single]
  ext b
  cases b <;> simp

@[simp]
theorem H_q0 : (H : 𝕢 →ₗ[ℂ] 𝕢) q0 = qplus := by
  ext b
  rw [show ((H : 𝕢 →ₗ[ℂ] 𝕢)) = matOp hMat from rfl, q0, matOp_single]
  cases b <;> simp [hMat, qplus]

@[simp]
theorem H_q1 : (H : 𝕢 →ₗ[ℂ] 𝕢) q1 = qminus := by
  ext b
  rw [show ((H : 𝕢 →ₗ[ℂ] 𝕢)) = matOp hMat from rfl, q1, matOp_single]
  cases b <;> simp [hMat, qminus]

/-! ## G-3: two-qubit gates and the controlled-gate combinator -/

/-- The controlled-NOT gate, the basis permutation `(a, b) ↦ (a, a ⊕ b)`. -/
noncomputable def CNOT : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)) :=
  permOp ⟨fun p => (p.1, xor p.1 p.2), fun p => (p.1, xor p.1 p.2), by decide, by decide⟩

/-- The swap gate, the basis permutation `(a, b) ↦ (b, a)`. -/
noncomputable def SWAP : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)) :=
  permOp (Equiv.prodComm Bool Bool)

/-- The controlled-`Z` gate, the diagonal `diag(1, 1, 1, -1)`. -/
noncomputable def CZ : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)) :=
  diagOp (fun p => if p.1 && p.2 then -1 else 1)
    (by rintro ⟨a, b⟩; cases a <;> cases b <;> simp)

@[simp]
theorem CNOT_single (a b : Bool) (c : ℂ) :
    (CNOT : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
      (EuclideanSpace.single (a, b) c) = EuclideanSpace.single (a, xor a b) c :=
  permOp_single _ _ _

@[simp]
theorem SWAP_single (a b : Bool) (c : ℂ) :
    (SWAP : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
      (EuclideanSpace.single (a, b) c) = EuclideanSpace.single (b, a) c :=
  permOp_single _ _ _

@[simp]
theorem CZ_single (a b : Bool) (c : ℂ) :
    (CZ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
      (EuclideanSpace.single (a, b) c)
      = EuclideanSpace.single (a, b) ((if a && b then -1 else 1) * c) :=
  diagOp_single _ _ _ _

section Control

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The matrix of a bundled unitary on a Euclidean space. -/
noncomputable def unitaryMat (U : UnitaryOp (EuclideanSpace ℂ β)) : Matrix β β ℂ :=
  Matrix.toEuclideanLin.symm (U : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β)

@[simp]
theorem matOp_unitaryMat (U : UnitaryOp (EuclideanSpace ℂ β)) :
    matOp (unitaryMat U) = (U : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) :=
  Matrix.toEuclideanLin.apply_symm_apply _

/-- The matrix of a unitary is a unitary matrix. -/
theorem unitaryMat_conjTranspose_mul (U : UnitaryOp (EuclideanSpace ℂ β)) :
    (unitaryMat U)ᴴ * unitaryMat U = 1 := by
  refine Matrix.toEuclideanLin.injective ?_
  change matOp _ = matOp _
  rw [matOp_mul, ← adjoint_matOp, matOp_unitaryMat, matOp_one]
  exact U.isUnitary.1

/-- The block-diagonal matrix `1 ⊕ U` of the controlled gate, on `Bool × β`
with the `Bool` factor as control. -/
noncomputable def controlMat (U : UnitaryOp (EuclideanSpace ℂ β)) :
    Matrix (Bool × β) (Bool × β) ℂ :=
  (Matrix.blockDiagonal fun b : Bool => if b then unitaryMat U else 1).submatrix
    (Equiv.prodComm Bool β) (Equiv.prodComm Bool β)

/-- The controlled gate `control U`: apply `U` to the target when the control
qubit is `true`, and nothing when it is `false`. CoqQ `BControl`. -/
noncomputable def control (U : UnitaryOp (EuclideanSpace ℂ β)) :
    UnitaryOp (EuclideanSpace ℂ (Bool × β)) :=
  unitaryOfMat (controlMat U) <| by
    have h : (Matrix.blockDiagonal fun b : Bool => if b then unitaryMat U else 1)ᴴ *
        (Matrix.blockDiagonal fun b : Bool => if b then unitaryMat U else 1) = 1 := by
      rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
      have hb : (fun b : Bool =>
          (if b then unitaryMat U else 1)ᴴ * (if b then unitaryMat U else 1))
          = fun _ : Bool => (1 : Matrix β β ℂ) := by
        funext b
        cases b
        · simp
        · simpa using unitaryMat_conjTranspose_mul U
      rw [hb]
      exact Matrix.blockDiagonal_one
    rw [controlMat, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, h,
      Matrix.submatrix_one_equiv]

end Control

/-- The matrix of the Pauli `X` gate. -/
theorem unitaryMat_X :
    unitaryMat X = Matrix.of fun a b : Bool => if a = !b then (1 : ℂ) else 0 := by
  refine Matrix.toEuclideanLin.injective ?_
  change matOp _ = matOp _
  rw [matOp_unitaryMat]
  refine LinearMap.ext fun v => ?_
  ext i
  rw [matOp_apply]
  cases i <;> simp [X]

/-- `CNOT` is the controlled `X` gate. -/
theorem CNOT_eq_control_X : CNOT = control X := by
  refine Subtype.ext (LinearMap.ext fun v => ?_)
  ext i
  obtain ⟨a, b⟩ := i
  rw [show ((control X : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool)))
    = matOp (controlMat X) from rfl, matOp_apply]
  simp only [controlMat, unitaryMat_X, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
    Equiv.prodComm_apply, Prod.swap_prod_mk, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;> simp [CNOT]

/-! ### The Hadamard gate on the diagonal kets

`H` is an involution, so the two computations `H_q0`/`H_q1` read backwards give
its action on `∣+⟩`/`∣-⟩`. They are proved here coordinatewise, from the
definitions of `qplus`/`qminus` and `inv_sqrt_two_mul_self`. -/

@[simp]
theorem H_qplus : (H : 𝕢 →ₗ[ℂ] 𝕢) qplus = q0 := by
  rw [qplus, map_smul, map_add, H_q0, H_q1, qplus, qminus]
  ext b
  cases b
  · simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul, q0_apply, q1_apply]
    norm_num
    linear_combination (2 : ℂ) * inv_sqrt_two_mul_self
  · simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul, q0_apply, q1_apply]
    norm_num

@[simp]
theorem H_qminus : (H : 𝕢 →ₗ[ℂ] 𝕢) qminus = q1 := by
  rw [qminus, map_smul, map_sub, H_q0, H_q1, qplus, qminus]
  ext b
  cases b
  · simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul, q0_apply, q1_apply]
    norm_num
  · simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul, q0_apply, q1_apply]
    norm_num
    linear_combination (2 : ℂ) * inv_sqrt_two_mul_self

/-! ### Inner products of the standard kets

The rank-one/effect algebra of a qubit derivation (predicate transformers on
`∣ψ⟩⟨ψ∣` effects) reduces to these numbers. -/

section Inner

open scoped ComplexInnerProductSpace

theorem inner_q0_q0 : (⟪q0, q0⟫ : ℂ) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_q0]; norm_num

theorem inner_q1_q1 : (⟪q1, q1⟫ : ℂ) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_q1]; norm_num

theorem inner_q0_q1 : (⟪q0, q1⟫ : ℂ) = 0 := by
  simp [q0, q1, EuclideanSpace.inner_single_left]

theorem inner_q1_q0 : (⟪q1, q0⟫ : ℂ) = 0 := by
  simp [q0, q1, EuclideanSpace.inner_single_left]

theorem inner_q0_qminus : (⟪q0, qminus⟫ : ℂ) = (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [qminus, inner_smul_right, inner_sub_right, inner_q0_q0, inner_q0_q1]
  ring

theorem inner_q0_qplus : (⟪q0, qplus⟫ : ℂ) = (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [qplus, inner_smul_right, inner_add_right, inner_q0_q0, inner_q0_q1]
  ring

end Inner

/-! ### The phase gate on the basis kets, the `T` gate, and the basis decomposition

The parameterised phase gate is a diagonal gate, so its basis actions are one
`diagOp_single` each. The `T` gate is its eighth-turn instance `phase (π/4)`,
the non-Clifford atom of the Clifford+`T` gate set. `qubit_decomp` writes an
arbitrary qubit vector as the coordinate combination of `∣0⟩` and `∣1⟩` — the
step that extends a pair of basis-ket computations to every input state. -/

/-- The phase gate fixes `∣0⟩`. -/
@[simp]
theorem phase_q0 (θ : ℝ) : (phase θ : 𝕢 →ₗ[ℂ] 𝕢) q0 = q0 := by
  rw [phase, q0, diagOp_single]
  norm_num

/-- The phase gate multiplies `∣1⟩` by `e^{iθ}`. -/
theorem phase_q1 (θ : ℝ) :
    (phase θ : 𝕢 →ₗ[ℂ] 𝕢) q1 = Complex.exp ((θ : ℂ) * Complex.I) • q1 := by
  rw [phase, q1, diagOp_single]
  ext b
  cases b <;> simp

/-- The `T` gate `diag(1, e^{iπ/4})`, the eighth-turn phase gate — the
non-Clifford atom of the Clifford+`T` gate set. -/
noncomputable def T : UnitaryOp 𝕢 := phase (Real.pi / 4)

/-- `T` fixes `∣0⟩`. -/
@[simp]
theorem T_q0 : (T : 𝕢 →ₗ[ℂ] 𝕢) q0 = q0 := phase_q0 _

/-- `T` multiplies `∣1⟩` by `e^{iπ/4}`. -/
theorem T_q1 :
    (T : 𝕢 →ₗ[ℂ] 𝕢) q1 = Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) • q1 :=
  phase_q1 _

/-- Every qubit vector is the coordinate combination of the two basis kets. -/
theorem qubit_decomp (χ : 𝕢) : χ = χ false • q0 + χ true • q1 := by
  ext b
  cases b <;> simp

end Qhl
