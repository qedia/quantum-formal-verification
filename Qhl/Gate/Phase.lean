import Qhl.Gate.Qubit

/-!
# Phase states, the controlled phase gate, and pair vectors

The gate-level atoms needed by the QFT example, mirroring CoqQ's
`src/example/coqq_paper/example.v:154-224` (`QuantumFourierTransform`), whose
inner loop is `[ut (s.1, s.2.[i]) := BControl (PhGate (omegan i))]`.

* `qbit b` — the computational basis ket `∣b⟩` indexed by a `Bool` (CoqQ `''b`),
  and `bitVal b` — the bit as a real number (CoqQ `b%:R`).
* `phaseKet θ` — the relative-phase state `(∣0⟩ + e^{iθ}∣1⟩)/√2`, CoqQ `'ph r`
  (`qtype.v:257`, `phstateE` at `qtype.v:266`; there the phase is `expip (2 r)`,
  here it is the angle `θ` itself). The Hadamard gate maps each basis ket onto
  a phase state (`H_qbit`) and `phase θ` (CoqQ `PhGate`, `qtype.v:235`) advances
  its parameter (`phase_phaseKet`) — the two moves of one QFT stage.
* `vpair u v` — the two-factor product vector `u ⊗ v` on
  `EuclideanSpace ℂ (α × β)`, the binary case of `prodV`
  (`Qhl/HSpace/LocalGate.lean`, CoqQ `tenvm` of `dirac/hstensor.v`).
* `cphase θ = control (phase θ)` — CoqQ `BControl (PhGate r)` — with its action
  on a pair `u ⊗ ∣b⟩` (`cphase_vpair`): the controlled phase is symmetric in its
  two wires, so it feeds the phase `bitVal b * θ` back into the *first* factor,
  which is exactly the QFT accumulation step.
-/

namespace Qhl

open scoped Matrix

/-! ## Basis kets indexed by a bit -/

/-- The computational basis ket `∣b⟩` as a function of the bit `b`. CoqQ `''b`
(`qtype.v`). -/
noncomputable def qbit (b : Bool) : 𝕢 := EuclideanSpace.single b 1

@[simp]
theorem qbit_false : qbit false = q0 := rfl

@[simp]
theorem qbit_true : qbit true = q1 := rfl

@[simp]
theorem norm_qbit (b : Bool) : ‖qbit b‖ = 1 := by cases b <;> simp

/-- The bit `b` as a real number, `0` or `1`. CoqQ `b%:R`. -/
def bitVal (b : Bool) : ℝ := if b then 1 else 0

@[simp]
theorem bitVal_false : bitVal false = 0 := rfl

@[simp]
theorem bitVal_true : bitVal true = 1 := rfl

/-! ## The phase state `'ph θ` -/

/-- The relative-phase state `(∣0⟩ + e^{iθ}∣1⟩)/√2`. CoqQ `'ph r`
(`qtype.v:257`), whose defining equation `phstateE` (`qtype.v:266`) is this
combination with `expip (2 r)` in place of `e^{iθ}`. -/
noncomputable def phaseKet (θ : ℝ) : 𝕢 :=
  (Real.sqrt 2 : ℂ)⁻¹ • (q0 + Complex.exp (θ * Complex.I) • q1)

/-- The coordinates of a phase state: `1/√2` on `∣0⟩` and `e^{iθ}/√2` on `∣1⟩`. -/
theorem phaseKet_apply (θ : ℝ) (b : Bool) :
    phaseKet θ b = (Real.sqrt 2 : ℂ)⁻¹ * (if b then Complex.exp (θ * Complex.I) else 1) := by
  cases b <;> simp [phaseKet]

@[simp]
theorem norm_phaseKet (θ : ℝ) : ‖phaseKet θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [phaseKet_apply, Fintype.sum_bool, Complex.norm_exp_ofReal_mul_I,
    Real.sq_sqrt, ← Real.sqrt_inv]

/-- At `θ = 0` the phase state is `∣+⟩`. CoqQ `phstate0`. -/
theorem phaseKet_zero : phaseKet 0 = qplus := by
  simp [phaseKet, qplus]

/-- At `θ = π` the phase state is `∣-⟩`, since `e^{iπ} = -1`. -/
theorem phaseKet_pi : phaseKet Real.pi = qminus := by
  rw [phaseKet, qminus, Complex.exp_pi_mul_I]
  simp [sub_eq_add_neg]

/-- The Hadamard gate sends the basis ket `∣b⟩` to the phase state of angle
`b·π`: `∣0⟩ ↦ ∣+⟩` and `∣1⟩ ↦ ∣-⟩`. This is the first move of a QFT stage
(CoqQ `[ut s.[i] := ''H]`, `example.v:169`). -/
theorem H_qbit (b : Bool) :
    (H : 𝕢 →ₗ[ℂ] 𝕢) (qbit b) = phaseKet (bitVal b * Real.pi) := by
  cases b
  · rw [qbit_false, H_q0, bitVal_false, zero_mul, phaseKet_zero]
  · rw [qbit_true, H_q1, bitVal_true, one_mul, phaseKet_pi]

/-! ## Diagonal gates coordinatewise -/

section Diag

variable {α : Type*} [Fintype α] [DecidableEq α]

-- `diagOp_apply` is provided upstream by `Qhl/Gate/Qubit.lean` (imported here).

/-- The matrix of a diagonal gate is the diagonal matrix. -/
theorem unitaryMat_diagOp (d : α → ℂ) (hd : ∀ a, ‖d a‖ = 1) :
    unitaryMat (diagOp d hd) = Matrix.diagonal d := by
  refine Matrix.toEuclideanLin.injective ?_
  change matOp _ = matOp _
  rw [matOp_unitaryMat]
  rfl

end Diag

/-- The phase gate acts coordinatewise: it multiplies the `∣1⟩` coordinate by
`e^{iθ}`. -/
theorem phase_apply (θ : ℝ) (v : 𝕢) (b : Bool) :
    (phase θ : 𝕢 →ₗ[ℂ] 𝕢) v b = (if b then Complex.exp (θ * Complex.I) else 1) * v b :=
  diagOp_apply _ _ _ _

/-- The matrix of the phase gate. -/
theorem unitaryMat_phase (θ : ℝ) :
    unitaryMat (phase θ)
      = Matrix.diagonal (fun b : Bool => if b then Complex.exp (θ * Complex.I) else 1) :=
  unitaryMat_diagOp _ _

/-- The phase gate advances the parameter of a phase state:
`PhGate θ' ('ph φ) = 'ph (φ + θ')`. This is the accumulation step of the QFT
(CoqQ `PhGate`, `qtype.v:235`). -/
theorem phase_phaseKet (θ' φ : ℝ) :
    (phase θ' : 𝕢 →ₗ[ℂ] 𝕢) (phaseKet φ) = phaseKet (φ + θ') := by
  ext b
  rw [phase_apply, phaseKet_apply, phaseKet_apply]
  cases b
  · simp
  · simp only [↓reduceIte, Complex.ofReal_add, add_mul, Complex.exp_add]
    ring

/-! ## Pair vectors -/

section Pair

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The two-factor product vector `u ⊗ v`, with coordinates
`(u ⊗ v) (a, b) = u a * v b`. This is the binary case of `prodV`
(`Qhl/HSpace/LocalGate.lean`), i.e. CoqQ `tenvm` (`dirac/hstensor.v`) on a
two-cell register. -/
noncomputable def vpair (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) :
    EuclideanSpace ℂ (α × β) :=
  WithLp.toLp 2 fun p => u p.1 * v p.2

@[simp]
theorem vpair_apply (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) (p : α × β) :
    vpair u v p = u p.1 * v p.2 := rfl

/-- The product of two basis kets is the basis ket of the pair. CoqQ
`tenvm_dv`. -/
theorem vpair_single (a : α) (b : β) (c d : ℂ) :
    vpair (EuclideanSpace.single a c) (EuclideanSpace.single b d)
      = EuclideanSpace.single (a, b) (c * d) := by
  ext p
  obtain ⟨x, y⟩ := p
  simp only [vpair_apply, PiLp.single_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The product vector is linear in its left factor. -/
theorem vpair_smul_left (c : ℂ) (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) :
    vpair (c • u) v = c • vpair u v := by
  ext p
  simp [mul_assoc]

/-- The product vector is additive in its left factor. -/
theorem vpair_add_left (u u' : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) :
    vpair (u + u') v = vpair u v + vpair u' v := by
  ext p
  simp [add_mul]

/-- The norm of a product vector is the product of the norms. CoqQ
`tenvm_norm`. -/
theorem norm_vpair (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) :
    ‖vpair u v‖ = ‖u‖ * ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    ← Real.sqrt_mul (by positivity)]
  congr 1
  simp only [vpair_apply, norm_mul, mul_pow, Fintype.sum_prod_type, ← Finset.mul_sum,
    ← Finset.sum_mul]

end Pair

/-! ## The controlled phase gate -/

/-- The controlled phase gate on two qubits: `∣c, t⟩ ↦ e^{iθ·c·t}∣c, t⟩`.
CoqQ `BControl (PhGate r)` (`example.v:164`). -/
noncomputable def cphase (θ : ℝ) : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)) :=
  control (phase θ)

/-- The controlled phase gate is diagonal: it multiplies the `∣1, 1⟩`
coordinate by `e^{iθ}` and fixes the other three. In particular it is
symmetric in its two wires. -/
theorem cphase_apply (θ : ℝ) (v : EuclideanSpace ℂ (Bool × Bool)) (p : Bool × Bool) :
    (cphase θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool)) v p
      = (if p.1 && p.2 then Complex.exp (θ * Complex.I) else 1) * v p := by
  obtain ⟨a, b⟩ := p
  rw [show ((cphase θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool)))
      = matOp (controlMat (phase θ)) from rfl, matOp_apply]
  simp only [controlMat, unitaryMat_phase, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
    Equiv.prodComm_apply, Prod.swap_prod_mk, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;> simp

/-- The action of the controlled phase on a product vector whose *second*
factor is a basis ket: the gate is diagonal and symmetric in its wires, so it
applies `PhGate (b·θ)` to the first factor. This is CoqQ's
`[ut (s.1, s.2.[i]) := BControl (PhGate (omegan i))]` step (`example.v:164`)
seen on a product state. -/
theorem cphase_vpair (θ : ℝ) (u : 𝕢) (b : Bool) :
    (cphase θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair u (qbit b))
      = vpair ((phase (bitVal b * θ) : 𝕢 →ₗ[ℂ] 𝕢) u) (qbit b) := by
  ext p
  obtain ⟨c, t⟩ := p
  rw [cphase_apply, vpair_apply, vpair_apply, phase_apply]
  cases b <;> cases c <;> cases t <;> simp

/-- The QFT accumulation step: a controlled phase with a basis ket on the
control wire advances the phase parameter of the other wire by `b·θ`. -/
theorem cphase_vpair_phaseKet (θ φ : ℝ) (b : Bool) :
    (cphase θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair (phaseKet φ) (qbit b))
      = vpair (phaseKet (φ + bitVal b * θ)) (qbit b) := by
  rw [cphase_vpair, phase_phaseKet]

/-- The swap gate exchanges the two factors of a product vector. Used by the
reversal circuit that closes the QFT (CoqQ `rev_circuit`, `example.v:140`). -/
theorem SWAP_vpair (u v : 𝕢) :
    (SWAP : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair u v) = vpair v u := by
  ext p
  obtain ⟨a, b⟩ := p
  simp only [SWAP, permOp_apply, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk,
    vpair_apply]
  exact mul_comm _ _

/-- The action of `CNOT` on a product of basis kets:
`∣a⟩ ⊗ ∣b⟩ ↦ ∣a⟩ ⊗ ∣a ⊕ b⟩` (`CNOT_single` read on a `vpair`). -/
theorem CNOT_vpair (a b : Bool) :
    (CNOT : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair (qbit a) (qbit b)) = vpair (qbit a) (qbit (xor a b)) := by
  simp only [qbit, vpair_single, one_mul, CNOT_single]

end Qhl
