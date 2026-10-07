import Qhl.Gate.Phase

/-!
# Controlled-`U` and phase kickback

The gate-level layer of quantum phase estimation, mirroring CoqQ's
`src/example/coqq_paper/example.v:980-999` (`PhaseEstimation`), whose oracle
stage is `[ut (x,y) := Uf ]` with `Uf := Multiplexer (fun i => U ^+ i)` — a
multiplexer whose one-control-bit rung is CoqQ's `BControl` (`control` here,
`Qhl/Gate/Qubit.lean`).

Everything is generic in the target space `EuclideanSpace ℂ β`; the control
wire is a single qubit `𝕢`, so the ambient space is `EuclideanSpace ℂ (Bool × β)`
and product states are the `vpair`s of `Qhl/Gate/Phase.lean`.

* `control_vpair_apply` — the defining action law of `BControl` on a product
  vector, read coordinatewise: the `false` block is the identity, the `true`
  block is `U`.
* `unitary_pow_eigen` — an eigenvector of `V` with eigenvalue `e^{iθ}` is an
  eigenvector of `V ^ m` with eigenvalue `e^{i·m·θ}`. This is CoqQ's `eigUn`
  (`example.v:990`), stated for the power `U ^+ m` itself rather than for its
  adjoint.
* `control_vpair_eigen` — **phase kickback**, the crux: when the target factor
  is an eigenvector of `V`, the controlled gate leaves it untouched and the
  eigenphase reappears on the *control* factor as `PhGate θ`.
* `control_pow_vpair_phaseKet` — the packaged rung: a controlled `V ^ m` on a
  phase state advances its parameter by `m·θ`, the phase-estimation analogue of
  the QFT accumulation step `cphase_vpair_phaseKet`.
-/

namespace Qhl

open scoped Matrix

/-! ## Powers of a bundled unitary on an eigenvector -/

/-- An eigenvector of `V` with eigenvalue `e^{iθ}` is an eigenvector of every
power `V ^ m`, with eigenvalue `e^{i·m·θ}`. CoqQ `eigUn`
(`example/coqq_paper/example.v:990`), there stated for the adjoint of `U ^+ m`;
here for the power itself. -/
theorem unitary_pow_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (V : UnitaryOp E) {w : E} {θ : ℝ}
    (hV : (V : E →ₗ[ℂ] E) w = Complex.exp ((θ : ℂ) * Complex.I) • w) (m : ℕ) :
    ((V ^ m : UnitaryOp E) : E →ₗ[ℂ] E) w
      = Complex.exp ((((m : ℝ) * θ : ℝ) : ℂ) * Complex.I) • w := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, UnitaryOp.coe_mul, LinearMap.comp_apply, hV, map_smul, ih, smul_smul,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-! ## The action of a controlled gate on a product vector -/

section Control

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The defining action law of the controlled gate `BControl V` on a product
vector: the `false` block of the control is the identity and the `true` block
is `V`. CoqQ `BControl` (`example.v:164`, `qtype.v`). -/
theorem control_vpair_apply (V : UnitaryOp (EuclideanSpace ℂ β)) (u : 𝕢)
    (w : EuclideanSpace ℂ β) (p : Bool × β) :
    (control V : EuclideanSpace ℂ (Bool × β) →ₗ[ℂ] EuclideanSpace ℂ (Bool × β)) (vpair u w) p
      = if p.1 then u true * ((V : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) w) p.2
        else u false * w p.2 := by
  obtain ⟨a, x⟩ := p
  rw [show ((control V : EuclideanSpace ℂ (Bool × β) →ₗ[ℂ] EuclideanSpace ℂ (Bool × β)))
      = matOp (controlMat V) from rfl, matOp_apply]
  simp only [controlMat, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
    Equiv.prodComm_apply, Prod.swap_prod_mk, Fintype.sum_prod_type, Fintype.sum_bool,
    vpair_apply]
  cases a
  · simp [Matrix.one_apply]
  · rw [← matOp_unitaryMat V, matOp_apply, Finset.mul_sum]
    simp [mul_left_comm]

/-- **Phase kickback.** If the target factor `w` is an eigenvector of `V` with
eigenvalue `e^{iθ}`, then the controlled gate fixes `w` and deposits the phase
on the *control* factor, where it acts as `PhGate θ`. This is the hypothesis
`eigU` of CoqQ's `PhaseEstimation` (`example.v:984`) seen through one rung of
the multiplexer `Uf`. -/
theorem control_vpair_eigen (V : UnitaryOp (EuclideanSpace ℂ β)) {w : EuclideanSpace ℂ β}
    {θ : ℝ}
    (hV : (V : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) w
        = Complex.exp ((θ : ℂ) * Complex.I) • w) (u : 𝕢) :
    (control V : EuclideanSpace ℂ (Bool × β) →ₗ[ℂ] EuclideanSpace ℂ (Bool × β))
        (vpair u w)
      = vpair ((phase θ : 𝕢 →ₗ[ℂ] 𝕢) u) w := by
  have hw : ∀ y : β, ((V : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) w) y
      = Complex.exp ((θ : ℂ) * Complex.I) * w y := by
    intro y
    rw [hV]
    simp
  ext p
  obtain ⟨a, x⟩ := p
  rw [control_vpair_apply, vpair_apply, phase_apply]
  cases a
  · simp
  · rw [hw]
    simp only [if_true]
    ring

/-- The phase-estimation rung: the controlled `V ^ m`, applied to a phase state
on the control wire and an eigenvector of `V` on the target wire, advances the
phase parameter by `m·θ` and leaves the eigenvector alone. This is CoqQ's
`Uf := Multiplexer (fun i => U ^+ i)` (`example.v:997-999`) at one control bit,
the phase-estimation analogue of the QFT step `cphase_vpair_phaseKet`. -/
theorem control_pow_vpair_phaseKet (V : UnitaryOp (EuclideanSpace ℂ β))
    {w : EuclideanSpace ℂ β} {θ : ℝ}
    (hV : (V : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) w
        = Complex.exp ((θ : ℂ) * Complex.I) • w) (m : ℕ) (φ : ℝ) :
    (control (V ^ m) : EuclideanSpace ℂ (Bool × β) →ₗ[ℂ] EuclideanSpace ℂ (Bool × β))
        (vpair (phaseKet φ) w)
      = vpair (phaseKet (φ + (m : ℝ) * θ)) w := by
  rw [control_vpair_eigen _ (unitary_pow_eigen V hV m), phase_phaseKet]

/-- The controlled gate is the identity on a product vector whose control
factor is `∣0⟩`: the `false` block of `BControl` is `1`. -/
theorem control_vpair_q0 (V : UnitaryOp (EuclideanSpace ℂ β)) (w : EuclideanSpace ℂ β) :
    (control V : EuclideanSpace ℂ (Bool × β) →ₗ[ℂ] EuclideanSpace ℂ (Bool × β))
        (vpair q0 w) = vpair q0 w := by
  ext p
  obtain ⟨a, x⟩ := p
  rw [control_vpair_apply, vpair_apply]
  cases a <;> simp

/-- The controlled gate applies `V` to the target factor of a product vector
whose control factor is `∣1⟩`: the `true` block of `BControl` is `V`. -/
theorem control_vpair_q1 (V : UnitaryOp (EuclideanSpace ℂ β)) (w : EuclideanSpace ℂ β) :
    (control V : EuclideanSpace ℂ (Bool × β) →ₗ[ℂ] EuclideanSpace ℂ (Bool × β))
        (vpair q1 w)
      = vpair q1 ((V : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) w) := by
  ext p
  obtain ⟨a, x⟩ := p
  rw [control_vpair_apply, vpair_apply]
  cases a <;> simp

end Control

/-! ## Gates acting on the first factor only

The companion of `control`: a gate applied to the **first** factor of
`EuclideanSpace ℂ (α × β)` and the identity on the second, i.e. `G ⊗ 1`. It is
built exactly like `controlMat`, from a `Matrix.blockDiagonal` — here the same
block `G` in every `β`-slot instead of `1`/`G` in the two control slots — so
unitarity is again `blockDiagonal_conjTranspose` + `blockDiagonal_mul` +
`blockDiagonal_one`.

Together with `control`, this is all the gate algebra needed to write a
two-wire circuit `(X ⊗ 1) · (control V) · (H ⊗ 1)` such as the repeat-until-
success rotation block. -/

section FirstFactor

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The block-diagonal matrix `G ⊗ 1` on `α × β`, with the `α` factor carrying
the gate. -/
noncomputable def fstMat (G : UnitaryOp (EuclideanSpace ℂ α)) :
    Matrix (α × β) (α × β) ℂ :=
  Matrix.blockDiagonal fun _ : β => unitaryMat G

/-- The gate `G ⊗ 1`: `G` on the first factor of `EuclideanSpace ℂ (α × β)`,
the identity on the second. -/
noncomputable def fstU (G : UnitaryOp (EuclideanSpace ℂ α)) :
    UnitaryOp (EuclideanSpace ℂ (α × β)) :=
  unitaryOfMat (fstMat (β := β) G) <| by
    rw [fstMat, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    rw [show (fun _ : β => (unitaryMat G)ᴴ * unitaryMat G) = fun _ : β => (1 : Matrix α α ℂ) from
      funext fun _ => unitaryMat_conjTranspose_mul G]
    exact Matrix.blockDiagonal_one

/-- **The action law of `G ⊗ 1`**: it does `G` to the first factor of a product
vector and leaves the second alone. -/
theorem fstU_vpair (G : UnitaryOp (EuclideanSpace ℂ α)) (u : EuclideanSpace ℂ α)
    (w : EuclideanSpace ℂ β) :
    (fstU (β := β) G : EuclideanSpace ℂ (α × β) →ₗ[ℂ] EuclideanSpace ℂ (α × β)) (vpair u w)
      = vpair ((G : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α) u) w := by
  ext p
  obtain ⟨a, x⟩ := p
  rw [show ((fstU (β := β) G :
        EuclideanSpace ℂ (α × β) →ₗ[ℂ] EuclideanSpace ℂ (α × β)))
      = matOp (fstMat (β := β) G) from rfl, matOp_apply, vpair_apply,
    ← matOp_unitaryMat G, matOp_apply, Finset.sum_mul, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [fstMat, Matrix.blockDiagonal_apply, vpair_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc]

end FirstFactor

end Qhl
