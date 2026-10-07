import Qhl.Gate.Phase

/-!
# The heralded attempt-block contract `K₀ = a·V, K₁ = b·1`

The gate-level layer of a *heralded* repeat-until-success circuit, generic in
the data space `EuclideanSpace ℂ β` exactly as `Qhl/Gate/RUSBlock.lean` is: a
two-wire attempt unitary `W` on `EuclideanSpace ℂ (Bool × β)` (ancilla first),
initialised with the ancilla `∣0⟩` and read out by a computational-basis
measurement of the ancilla, whose two branch operators

```
K_i  =  (⟨i∣ ⊗ 1) · W · (∣0⟩ ⊗ 1)
```

are `K₀ = a·V` (heralded success: the outcome `0` applies the target gate `V`)
and `K₁ = b·1` (identity failure: the outcome `1` restores the data exactly),
with `|a|² + |b|² = 1`. This is the branch contract of the repeat-until-success
synthesis literature (Paetznick–Svore), separated from any concrete circuit:
a concrete Clifford+`T` block *satisfies* the contract, and the bounded-RUS
loop theorem (`Qhl/Logic/HeraldedRUS.lean`) *consumes* it.

* `vpair_add_right` — additivity of the pair vector in its second factor (the
  sibling of the library's `vpair_add_left`; the scalar law `vpair_smul_right`
  is already provided by `Qhl/Register/GraphState.lean`).
* `inner_vpair_vpair` — the pair-vector inner product `⟪u⊗v, u'⊗v'⟫ =
  ⟪u,u'⟫·⟪v,v'⟫` (CoqQ `tenvm_dot`, binary case).
* `pairIns u` — the insertion `v ↦ u ⊗ v` as a linear map, and `pairCtr u` —
  its adjoint, the contraction `⟨u∣ ⊗ 1`, with `inner_pairCtr` and
  `pairCtr_vpair`.
* `rowVec`, `vpair_rowVec_decomp`, `pairCtr_qbit` — the decomposition of an
  arbitrary vector of `EuclideanSpace ℂ (Bool × β)` into its two ancilla rows,
  and the contraction as the row extraction.
* `branchK W i = pairCtr ∣i⟩ ∘ W ∘ pairIns ∣0⟩` — the branch operator `K_i`.
* `HeraldedBlock W V a b` — the contract, a single decomposition law
  `W (∣0⟩ ⊗ χ) = a·(∣0⟩ ⊗ Vχ) + b·(∣1⟩ ⊗ χ)`, with the derived branch forms
  `branchK_false = a·V`, `branchK_true = b·1`, the normalisation
  `star_mul_sum : ā·a + b̄·b = 1` / `norm_sum : ‖a‖² + ‖b‖² = 1` (derived from
  the unitarity of `W`, never assumed), and the fused backward laws
  `ctr0_adjW_succ` / `ctr0_adjW_fail` that a backward predicate-transformer
  chain consumes.
* `adjoint_coe_congr` — transporting a unitary along an isometry equivalence
  commutes with the adjoint (`(congr e U)† = congr e U†`), the operator-level
  companion the whole-register lift of `W` needs.

Nothing here mentions a program, a register, a world or a Hoare triple: this
is the gate algebra only (ownership test), exactly as `Qhl/Gate/RUSBlock.lean`
is the gate algebra of the dilation-style RUS block.
-/

namespace Qhl

open scoped ComplexInnerProductSpace

/-! ## §1. Second-factor linearity and the pair-vector inner product -/

section PairAlgebra

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- The product vector is additive in its right factor (the sibling of the
library's `vpair_add_left`; the scalar law is `vpair_smul_right`,
`Qhl/Register/GraphState.lean`). -/
theorem vpair_add_right (u : EuclideanSpace ℂ α) (v v' : EuclideanSpace ℂ β) :
    vpair u (v + v') = vpair u v + vpair u v' := by
  ext p
  simp only [vpair_apply, PiLp.add_apply]
  ring

omit [DecidableEq α] [DecidableEq β] in
/-- The inner product of two pair vectors multiplies the factors' inner
products — CoqQ `tenvm_dot` on two factors, the `vpair` companion of the
library's `prodV_inner`. -/
theorem inner_vpair_vpair (u u' : EuclideanSpace ℂ α) (v v' : EuclideanSpace ℂ β) :
    (⟪vpair u v, vpair u' v'⟫ : ℂ) = ⟪u, u'⟫ * ⟪v, v'⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, vpair_apply, map_mul,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-! ## §2. The insertion `∣u⟩ ⊗ 1` and the contraction `⟨u∣ ⊗ 1` -/

/-- The insertion of a fixed first factor: `v ↦ u ⊗ v`, as a linear map. -/
noncomputable def pairIns (u : EuclideanSpace ℂ α) :
    EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ (α × β) where
  toFun v := vpair u v
  map_add' v v' := vpair_add_right u v v'
  map_smul' c v := by
    ext p
    simp only [vpair_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
@[simp]
theorem pairIns_apply (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) :
    pairIns u v = vpair u v := rfl

/-- The contraction `⟨u∣ ⊗ 1`: the adjoint of the insertion `pairIns u`. -/
noncomputable def pairCtr (u : EuclideanSpace ℂ α) :
    EuclideanSpace ℂ (α × β) →ₗ[ℂ] EuclideanSpace ℂ β :=
  LinearMap.adjoint (pairIns u)

omit [DecidableEq α] [DecidableEq β] in
/-- The defining adjunction of the contraction:
`⟪v, (⟨u∣ ⊗ 1) η⟫ = ⟪u ⊗ v, η⟫`. -/
theorem inner_pairCtr (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β)
    (η : EuclideanSpace ℂ (α × β)) :
    (⟪v, pairCtr u η⟫ : ℂ) = ⟪vpair u v, η⟫ := by
  rw [pairCtr, LinearMap.adjoint_inner_right, pairIns_apply]

omit [DecidableEq α] [DecidableEq β] in
/-- The contraction of a pair vector: `(⟨u∣ ⊗ 1)(u' ⊗ v) = ⟪u,u'⟫ • v`. -/
theorem pairCtr_vpair (u u' : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) :
    pairCtr u (vpair u' v) = (⟪u, u'⟫ : ℂ) • v := by
  refine ext_inner_left ℂ fun χ => ?_
  rw [inner_pairCtr, inner_vpair_vpair, inner_smul_right]

end PairAlgebra

/-! ## §3. The ancilla-row decomposition (first factor `Bool`) -/

section BoolRows

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The row of a two-factor vector at a fixed first bit `c`: the data-space
vector `d ↦ η (c, d)`. -/
noncomputable def rowVec (c : Bool) (η : EuclideanSpace ℂ (Bool × β)) :
    EuclideanSpace ℂ β :=
  WithLp.toLp 2 fun d => η (c, d)

omit [Fintype β] [DecidableEq β] in
@[simp]
theorem rowVec_apply (c : Bool) (η : EuclideanSpace ℂ (Bool × β)) (d : β) :
    rowVec c η d = η (c, d) := rfl

omit [Fintype β] [DecidableEq β] in
/-- Every vector of the ancilla–data space splits into its two ancilla rows. -/
theorem vpair_rowVec_decomp (η : EuclideanSpace ℂ (Bool × β)) :
    η = vpair q0 (rowVec false η) + vpair q1 (rowVec true η) := by
  ext p
  obtain ⟨c, d⟩ := p
  cases c <;>
    simp [vpair_apply, q0, q1]

omit [DecidableEq β] in
/-- The contraction at a basis bit extracts the corresponding row. -/
theorem pairCtr_qbit (c : Bool) (η : EuclideanSpace ℂ (Bool × β)) :
    pairCtr (qbit c) η = rowVec c η := by
  refine ext_inner_left ℂ fun χ => ?_
  rw [inner_pairCtr]
  simp only [PiLp.inner_apply, RCLike.inner_apply, vpair_apply, rowVec_apply, map_mul,
    Fintype.sum_prod_type, Fintype.sum_bool]
  cases c <;> simp [qbit]

end BoolRows

/-! ## §4. The adjoint of a transported unitary -/

section AdjointCongr

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Transporting a unitary along an isometry equivalence commutes with the
adjoint: `(congr e U)† = congr e (U†)` — the bundled form of
`adjoint_conj_isometryEquiv` (`Qhl/Gate/Unitary.lean`), with the adjoint of the
bundled gate being its `star`. -/
theorem adjoint_coe_congr (e : E ≃ₗᵢ[ℂ] F) (U : UnitaryOp E) :
    LinearMap.adjoint (UnitaryOp.congr e U : F →ₗ[ℂ] F)
      = (UnitaryOp.congr e (star U) : F →ₗ[ℂ] F) := by
  change LinearMap.adjoint (e.toLinearEquiv.conj (U : E →ₗ[ℂ] E)) = _
  rw [adjoint_conj_isometryEquiv]
  congr 1

end AdjointCongr

/-! ## §5. The branch operators and the heralded-block contract -/

section HeraldedBlock

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The branch operator `K_i = (⟨i∣ ⊗ 1) · W · (∣0⟩ ⊗ 1)` of the attempt
unitary `W`: reset the ancilla to `∣0⟩`, run `W`, read the ancilla outcome
`i`. -/
noncomputable def branchK (W : UnitaryOp (EuclideanSpace ℂ (Bool × β))) (i : Bool) :
    EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β :=
  pairCtr (qbit i)
    ∘ₗ (W : EuclideanSpace ℂ (Bool × β) →ₗ[ℂ] EuclideanSpace ℂ (Bool × β))
    ∘ₗ pairIns q0

/-- **The heralded attempt-block contract**: on an ancilla reset to `∣0⟩` the
attempt unitary decomposes as

```
W (∣0⟩ ⊗ χ) = a • (∣0⟩ ⊗ Vχ) + b • (∣1⟩ ⊗ χ),
```

i.e. `K₀ = a·V` (heralded success) and `K₁ = b·1` (identity failure) —
the branch form of the repeat-until-success synthesis literature
(Paetznick–Svore), with `|a|² + |b|² = 1` *derived* below from the unitarity
of `W`. -/
structure HeraldedBlock (W : UnitaryOp (EuclideanSpace ℂ (Bool × β)))
    (V : UnitaryOp (EuclideanSpace ℂ β)) (a b : ℂ) : Prop where
  /-- The two-branch decomposition of `W` on a reset ancilla. -/
  decomp : ∀ χ : EuclideanSpace ℂ β,
    (W : EuclideanSpace ℂ (Bool × β) →ₗ[ℂ] EuclideanSpace ℂ (Bool × β)) (vpair q0 χ)
      = a • vpair q0 ((V : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) χ)
        + b • vpair q1 χ

namespace HeraldedBlock

variable {W : UnitaryOp (EuclideanSpace ℂ (Bool × β))}
  {V : UnitaryOp (EuclideanSpace ℂ β)} {a b : ℂ}

omit [DecidableEq β] in
/-- `K₀ = a·V`: the outcome `0` heralds the target gate. -/
theorem branchK_false (hB : HeraldedBlock W V a b) :
    branchK W false = a • (V : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) := by
  refine LinearMap.ext fun χ => ?_
  rw [branchK]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, pairIns_apply, qbit_false]
  rw [hB.decomp χ, map_add, map_smul, map_smul, pairCtr_vpair, pairCtr_vpair,
    inner_q0_q0, inner_q0_q1, one_smul, zero_smul, smul_zero, add_zero]

omit [DecidableEq β] in
/-- `K₁ = b·1`: the outcome `1` restores the data exactly. -/
theorem branchK_true (hB : HeraldedBlock W V a b) :
    branchK W true = b • (1 : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) := by
  refine LinearMap.ext fun χ => ?_
  rw [branchK]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, pairIns_apply, qbit_true,
    Module.End.one_apply]
  rw [hB.decomp χ, map_add, map_smul, map_smul, pairCtr_vpair, pairCtr_vpair,
    inner_q1_q0, inner_q1_q1, one_smul, zero_smul, smul_zero, zero_add]

/-- **The normalisation, derived**: `ā·a + b̄·b = 1`, from the unitarity of `W`
evaluated at one unit data vector (`[Nonempty β]` supplies a basis ket). This
is the complex form the rank-one invariant algebra consumes. -/
theorem star_mul_sum [Nonempty β] (hB : HeraldedBlock W V a b) :
    star a * a + star b * b = 1 := by
  set χ : EuclideanSpace ℂ β := EuclideanSpace.single (Classical.arbitrary β) 1 with hχdef
  have hχ : (⟪χ, χ⟫ : ℂ) = 1 := by
    rw [hχdef]
    simp
  have hVχ : (⟪(V : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) χ,
      (V : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) χ⟫ : ℂ) = 1 := by
    rw [V.isUnitary.isIsometryOp χ χ, hχ]
  have h := congrArg (fun ξ => (⟪ξ, ξ⟫ : ℂ)) (hB.decomp χ)
  rw [W.isUnitary.isIsometryOp, inner_vpair_vpair, inner_q0_q0, hχ, mul_one] at h
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_vpair_vpair, inner_q0_q0, inner_q0_q1, inner_q1_q0, inner_q1_q1, hVχ, hχ,
    mul_one, mul_zero, zero_mul, add_zero, zero_add, starRingEnd_apply] at h
  rw [mul_comm (star a) a, mul_comm (star b) b]
  exact h.symm

/-- The real form of the normalisation: `‖a‖² + ‖b‖² = 1` — the success and
failure probabilities of one attempt sum to one. -/
theorem norm_sum [Nonempty β] (hB : HeraldedBlock W V a b) :
    ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
  have h := hB.star_mul_sum
  rw [show (star a * a : ℂ) = (starRingEnd ℂ) a * a from rfl,
    show (star b * b : ℂ) = (starRingEnd ℂ) b * b from rfl,
    RCLike.conj_mul, RCLike.conj_mul] at h
  exact Complex.ofReal_eq_one.mp (by push_cast; exact h)

omit [DecidableEq β] in
/-- **The fused backward success law** a backward predicate-transformer chain
consumes: contracting the reset ancilla out of `W†` applied to a success
profile is `ā • V†`,

```
(⟨0∣ ⊗ 1) W† (∣0⟩ ⊗ x) = star a • V† x .
```
-/
theorem ctr0_adjW_succ (hB : HeraldedBlock W V a b) (x : EuclideanSpace ℂ β) :
    pairCtr q0 (LinearMap.adjoint
        (W : EuclideanSpace ℂ (Bool × β) →ₗ[ℂ] EuclideanSpace ℂ (Bool × β))
        (vpair q0 x))
      = star a • LinearMap.adjoint
          (V : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ β) x := by
  refine ext_inner_left ℂ fun χ => ?_
  rw [inner_pairCtr, LinearMap.adjoint_inner_right, hB.decomp χ, inner_smul_right,
    LinearMap.adjoint_inner_right]
  simp only [inner_add_left, inner_smul_left, inner_vpair_vpair, inner_q0_q0, inner_q1_q0,
    one_mul, zero_mul, mul_zero, add_zero, starRingEnd_apply]

omit [DecidableEq β] in
/-- **The fused backward failure law**: contracting the reset ancilla out of
`W†` applied to a failure profile is `b̄ • 1`,

```
(⟨0∣ ⊗ 1) W† (∣1⟩ ⊗ x) = star b • x .
```
-/
theorem ctr0_adjW_fail (hB : HeraldedBlock W V a b) (x : EuclideanSpace ℂ β) :
    pairCtr q0 (LinearMap.adjoint
        (W : EuclideanSpace ℂ (Bool × β) →ₗ[ℂ] EuclideanSpace ℂ (Bool × β))
        (vpair q1 x))
      = star b • x := by
  refine ext_inner_left ℂ fun χ => ?_
  rw [inner_pairCtr, LinearMap.adjoint_inner_right, hB.decomp χ, inner_smul_right]
  simp only [inner_add_left, inner_smul_left, inner_vpair_vpair, inner_q0_q1, inner_q1_q1,
    one_mul, zero_mul, mul_zero, zero_add, starRingEnd_apply]

end HeraldedBlock

end HeraldedBlock

/-! ## §6. The subnormalised failure amplitude

The one further consequence of the derived normalisation that the
success-probability triple (`Qhl/Logic/HeraldedRUS.lean` §8) consumes: the
failure amplitude of one attempt satisfies `‖b‖ ≤ 1`, so the residual failure
mass `‖b‖^{2n}` of `n` attempts lies in `[0, 1]`. -/

section HeraldedBlockNorm

variable {β : Type*} [Fintype β] [DecidableEq β]
variable {W : UnitaryOp (EuclideanSpace ℂ (Bool × β))}
  {V : UnitaryOp (EuclideanSpace ℂ β)} {a b : ℂ}

/-- The failure amplitude of one attempt is subnormalised: `‖b‖ ≤ 1`, from the
derived normalisation `‖a‖² + ‖b‖² = 1`. -/
theorem HeraldedBlock.norm_b_le_one [Nonempty β] (hB : HeraldedBlock W V a b) :
    ‖b‖ ≤ 1 := by
  have hab := hB.norm_sum
  nlinarith [sq_nonneg ‖a‖, norm_nonneg b, sq_nonneg (‖b‖ - 1), sq_nonneg (‖b‖ + 1)]

end HeraldedBlockNorm

end Qhl
