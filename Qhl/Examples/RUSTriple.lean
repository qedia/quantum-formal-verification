import Qhl.Logic.AlmostSure
import Qhl.Logic.Frame
import Qhl.Logic.PreCompute
import Qhl.Gate.RUSBlock
import Qhl.Register.Qubits
import Qhl.Register.TwoQubits

/-!
# Repeat-Until-Success: the almost-surely-terminating `while` loop

The genuine probabilistic-termination example of `QHL⁺_tot`. The program is

```
succ := 0;
while succ = 0 do
  a := ∣0⟩;                    -- reset the ancilla
  (a, t) *= U_RUS;             -- the rotation block
  m := M[a];                   -- measure the ancilla
  succ := 1 - m                -- exit exactly when m = 0
od
```

over two qubit cells — the ancilla `a` (`false`) and the data wire `t`
(`true`) — with the two-bit classical store `(succ, m)`.

`U_RUS = (X ⊗ 1) · (control V) · (H ⊗ 1)` is the standard RUS block: on the
input `∣0⟩ₐ ⊗ ψ` it produces `2^{-1/2}(∣0⟩ₐ ⊗ Vψ + ∣1⟩ₐ ⊗ ψ)`, so the outcome
`m = 0` (probability `½`) leaves `V ψ` on the data wire and exits the loop,
while `m = 1` (probability `½`) restores `ψ` *exactly* and the loop retries.
Everything is generic in the single-qubit target gate `V` and in the unit data
ket `ψ₀`.

## Why this example exists

The loop **cannot** be discharged by the ranked rule `DerivTot.whileLoop`: no
`t : σT → ℕ` decreases at every iteration, because the retry branch returns the
store to its exact previous value. Termination here is *almost sure*, and it is
proved by the library rule `Qhl.validTot_while_ast` (`Qhl/Logic/AlmostSure.lean`),
the geometric-contraction case of quantum almost-sure termination: the
loop-continuation mass is multiplied by `c = ½` at every pass.

## The shape of the proof

The invariant is

```
J σ = if succ then ∣w⟩⟨w∣ else ∣v₀⟩⟨v₀∣ + ∣v₁⟩⟨v₁∣
```

with `v_b = ∣b⟩ₐ ⊗ ψ₀`, `w = ∣0⟩ₐ ⊗ Vψ₀`. Writing the `succ = 0` branch as the
**orthogonal decomposition** `∣v₀⟩⟨v₀∣ + ∣v₁⟩⟨v₁∣` of the effect `1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣`
is what makes every predicate transformer of the body collapse by pure
`outerLM` algebra — each of the four backward steps is one line of rank-one
arithmetic (`Qhl/Logic/Frame.lean` §7).

Two backward chains are computed through the body, for **every** store `σ`:

* the invariant chain, `J ⇜ ∣v₀⟩⟨v₀∣ + ∣v₁⟩⟨v₁∣` (`bodyPre_op`), which gives
  `{J ∧ b} body {J}` by (Ax-Init)+(Ax-Uni)+(Ax-Meas)+(Ax-Ass)+(R-Conseq);
* the complement chain, `(J ∧ b)ᶜ ⇜ 1 − ½·(∣v₀⟩⟨v₀∣ + ∣v₁⟩⟨v₁∣)`
  (`complPre_op`), which feeds `LoopBodyContraction.of_complement` with the
  contraction factor `c = ½` — the exact success probability of one pass.

The headline `rusValid` is the semantic triple
`{1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣} rusProg {succ ∧ ∣0⟩ₐ ⊗ ∣Vψ₀⟩}`, valid over **all** density
operators `ρ` (the library semantics is the density-matrix/effect one).
-/

namespace Qhl.RUS

open Qhl TwoQubits Finset
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal

/-! ## §1. The fixture: two qubit cells, a two-bit store -/

/-- The world: two cells, the ancilla `false` and the data wire `true`. -/
abbrev L : Type := Bool

/-- Both cells are qubits (the library's standard qubit-cell family). -/
abbrev D : L → Type := QubitCells L

/-- The classical store `(succ, m)`: the exit flag and the last outcome. -/
abbrev Store : Type := Bool × Bool

/-- The loop guard: keep going while `succ` is `false`. -/
def guard : Store → Bool := fun σ => !σ.1

theorem a_ne_t : (false : L) ≠ true := by decide

/-- The one-cell register of the ancilla. -/
abbrev regA : Reg L 1 := Reg.single false

/-- The two-cell register `(a, t)` of the rotation block. -/
abbrev regAT : Reg L 2 := Reg.pair false true a_ne_t

/-- The register expression of the ancilla (constant). -/
abbrev rA : RegExpr Store L 1 := RegExpr.const regA

/-- The register expression of the pair `(a, t)` (constant). -/
abbrev rAT : RegExpr Store L 2 := RegExpr.const regAT

/-- `succ := 0`. -/
def initSucc : Store → Store := fun σ => (false, σ.2)

/-- `m := ` the observed bit. -/
def updM : Fin 2 → Store → Store := fun i σ => (σ.1, finTwoEquiv i)

/-- `succ := 1 − m`. -/
def setSucc : Store → Store := fun σ => (!σ.2, σ.2)

@[simp] theorem updM_zero (σ : Store) : updM 0 σ = (σ.1, false) := rfl
@[simp] theorem updM_one (σ : Store) : updM 1 σ = (σ.1, true) := rfl

/-- The two outcomes as classical states of the ancilla's tuple space. -/
def outcomeEquiv : Fin 2 ≃ TIdx D (rA (false, false)) :=
  finTwoEquiv.trans (Equiv.funUnique (Fin 1) Bool).symm

/-- The computational-basis measurement of the ancilla. -/
noncomputable def meas (σ : Store) : QMeasure 2 (TSpace D (rA σ)) := basisMeas outcomeEquiv

/-- The two branch operators, unfolded once (the `rA`-dependent type of `meas`
blocks the equation-lemma rewrite, so it is pinned here by `rfl`). -/
theorem meas_M (i : Fin 2) :
    (meas (false, false)).M i
      = outerLM (EuclideanSpace.single (outcomeEquiv i) (1 : ℂ))
          (EuclideanSpace.single (outcomeEquiv i) (1 : ℂ)) := rfl

/-! ## §2. The RUS rotation block `U_RUS = (X ⊗ 1) · control V · (H ⊗ 1)`

The block and its three action laws are the *library's* (`Qhl/Gate/RUSBlock.lean`,
generic in the target space): `uRus V = fstU X * control V * fstU H` with

* `uRus_vpair_qminus` — the success branch read backwards
  (`∣-⟩ ⊗ χ ↦ ∣0⟩ ⊗ Vχ`),
* `uRus_vpair_qplus` — the retry branch read backwards (`∣+⟩ ⊗ χ ↦ ∣1⟩ ⊗ χ`),
* `uRus_vpair_q0` — the forward reading
  `U_RUS (∣0⟩ ⊗ χ) = 2^{-1/2}(∣0⟩ ⊗ Vχ + ∣1⟩ ⊗ χ)`: outcome `0` with
  probability `½` leaves `Vχ`, outcome `1` restores `χ` exactly.

Here the target space is the data qubit, `β = Bool`. -/

/-! ## §3. Two-wire product states — the library layer
`Qhl/Register/TwoQubits.lean` (`fam`/`gv` and their algebra, and the reset
channel `gKraus`/`dualInit_outerLM` of the cell `false`), and the ket inner
products of `Qhl/Gate/Qubit.lean`. Nothing two-wire is re-derived here. -/

/-! ## §4. The program -/

/-- `a := ∣0⟩`. The initialised cell set is `regA.sig`, so all the
initialisation algebra stays on the register's own labelled space. -/
noncomputable def resetAnc : Prog Store D := .init fun _ => regA.sig

/-- The rotation block transported to the tuple space of the register `(a, t)`
— the gate the program's `.unitary` node carries. -/
noncomputable def gateAT (V : UnitaryOp 𝕢) (_ : Store) : UnitaryOp (TSpace D regAT.toFun) :=
  pairGate (D := D) false true a_ne_t (uRus V)

/-- `(a, t) *= U_RUS`. -/
noncomputable def kickStep (V : UnitaryOp 𝕢) : Prog Store D :=
  Prog.unitary2 false true a_ne_t (uRus V)

theorem kickStep_eq (V : UnitaryOp 𝕢) : kickStep V = .unitary 2 rAT (gateAT V) := rfl

/-- `m := M[a]`. -/
noncomputable def measStep : Prog Store D := .measure 2 1 rA meas updM

/-- The loop body. -/
noncomputable def rusBody (V : UnitaryOp 𝕢) : Prog Store D :=
  .seq resetAnc (.seq (kickStep V) (.seq measStep (.assign setSucc)))

/-- The repeat-until-success loop. -/
noncomputable def rusLoop (V : UnitaryOp 𝕢) : Prog Store D := .while guard (rusBody V)

/-- **The program**: `succ := 0; while succ = 0 do body od`. -/
noncomputable def rusProg (V : UnitaryOp 𝕢) : Prog Store D :=
  .seq (.assign initSucc) (rusLoop V)

/-- The program really is the literal five-node tree, checked structurally. -/
example (V : UnitaryOp 𝕢) :
    rusProg V
      = Prog.seq (.assign initSucc)
          (.while guard
            (.seq (.init fun _ => regA.sig)
              (.seq (.unitary 2 rAT (gateAT V))
                (.seq (.measure 2 1 rA meas updM) (.assign setSucc))))) := rfl

/-! ## §5. The lifted operators of the three quantum statements -/

/-- The whole-world operator of the rotation block. -/
noncomputable def Kgate (V : UnitaryOp 𝕢) : EndM D (univ : Finset L) :=
  regLift regAT (gateAT V (false, false) : TSpace D regAT.toFun →ₗ[ℂ] TSpace D regAT.toFun)

/-- The whole-world operator of the measurement branch `i`. -/
noncomputable def Kmeas (i : Fin 2) : EndM D (univ : Finset L) :=
  regLift regA ((meas (false, false)).M i)

theorem regLift_rA (σ : Store) (h : Function.Injective (rA σ)) (i : Fin 2) :
    regLift (D := D) ⟨rA σ, h⟩ ((meas σ).M i) = Kmeas i := rfl

theorem regLift_rAT (V : UnitaryOp 𝕢) (σ : Store) (h : Function.Injective (rAT σ)) :
    regLift (D := D) ⟨rAT σ, h⟩
        (gateAT V σ : TSpace D (⟨rAT σ, h⟩ : Reg L 2).toFun →ₗ[ℂ] _) = Kgate V := rfl

theorem distA (σ : Store) : Function.Injective (rA σ) := regA.inj
theorem distAT (σ : Store) : Function.Injective (rAT σ) := regAT.inj

/-! ### The measurement operators -/

theorem meas_M_eq (i : Fin 2) :
    (meas (false, false)).M i
      = (tupleOne D false).toLinearEquiv.conj
          (outerLM (qbit (finTwoEquiv i)) (qbit (finTwoEquiv i))) := by
  have h : (tupleOne D false) (qbit (finTwoEquiv i))
      = EuclideanSpace.single (outcomeEquiv i) (1 : ℂ) := by
    rw [qbit, tupleOne, euclCongr_single]
    rfl
  rw [meas_M, conj_isometryEquiv_outerLM, h]

theorem regA_op_meas (i : Fin 2) :
    regA.op D ((meas (false, false)).M i)
      = singleOp D false (outerLM (qbit (finTwoEquiv i)) (qbit (finTwoEquiv i))) := by
  rw [meas_M_eq]
  exact reg_op_single D false _

/-- The branch operator on a two-wire product state: it projects the ancilla
factor onto `∣b⟩` and leaves the data wire alone. -/
theorem Kmeas_gv (i : Fin 2) (u v : 𝕢) :
    Kmeas i (gv u v)
      = (⟪qbit (finTwoEquiv i), u⟫ : ℂ) • gv (qbit (finTwoEquiv i)) v := by
  rw [Kmeas, regLift, regA_op_meas, gv, liftF_singleOp_prodV D false (subset_univ _),
    fam_false, outerLM_apply, fam_update_a, ← gv_smul_left]
  rfl

theorem adjoint_Kmeas (i : Fin 2) : LinearMap.adjoint (Kmeas i) = Kmeas i := by
  rw [Kmeas, adjoint_regLift regA ((meas (false, false)).M i)]
  congr 1
  rw [meas_M, adjoint_outerLM]

/-- The rank-one conjugation identity of the (self-adjoint) branch operator: the
predicate transformer of the measurement on a rank-one effect is again rank one. -/
private theorem Kmeas_conj_outer (i : Fin 2) (u v : HS D (univ : Finset L)) :
    Kmeas i ∘ₗ outerLM u v ∘ₗ Kmeas i = outerLM (Kmeas i u) (Kmeas i v) := by
  nth_rewrite 1 [← adjoint_Kmeas i]
  rw [adjoint_comp_outerLM_comp, adjoint_Kmeas]

theorem Kmeas_complete :
    LinearMap.adjoint (Kmeas 0) ∘ₗ Kmeas 0 + LinearMap.adjoint (Kmeas 1) ∘ₗ Kmeas 1 = 1 := by
  have h := isQMeasure_regLift regA (meas (false, false))
  rw [IsQMeasure, Fin.sum_univ_two] at h
  exact h

theorem Kmeas_zero_gv_q0 (v : 𝕢) : Kmeas 0 (gv q0 v) = gv q0 v := by
  rw [Kmeas_gv, show finTwoEquiv 0 = false from rfl, qbit_false, inner_q0_q0, one_smul]

theorem Kmeas_one_gv_q0 (v : 𝕢) : Kmeas 1 (gv q0 v) = 0 := by
  rw [Kmeas_gv, show finTwoEquiv 1 = true from rfl, qbit_true, inner_q1_q0, zero_smul]

theorem Kmeas_one_gv_q1 (v : 𝕢) : Kmeas 1 (gv q1 v) = gv q1 v := by
  rw [Kmeas_gv, show finTwoEquiv 1 = true from rfl, qbit_true, inner_q1_q1, one_smul]

/-! ### The rotation-block operator -/

theorem Kgate_gv (V : UnitaryOp 𝕢) {u v u' v' : 𝕢}
    (hG : (uRus V : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair u v) = vpair u' v') :
    Kgate V (gv u v) = gv u' v' := by
  rw [Kgate, gateAT, gv, regLift_pairGate_prodV false true a_ne_t (uRus V) (fam u v) hG,
    fam_update_both]
  rfl

theorem isUnitary_Kgate (V : UnitaryOp 𝕢) : IsUnitary (Kgate V) :=
  isUnitary_regLift regAT _

/-- The success branch read backwards: `∣0⟩ ⊗ Vχ ↤ ∣-⟩ ⊗ χ`. -/
theorem adjoint_Kgate_w (V : UnitaryOp 𝕢) (χ : 𝕢) :
    LinearMap.adjoint (Kgate V) (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) χ)) = gv qminus χ := by
  rw [← Kgate_gv V (uRus_vpair_qminus V χ), adjoint_apply_apply (isUnitary_Kgate V)]

/-- The retry branch read backwards: `∣1⟩ ⊗ χ ↤ ∣+⟩ ⊗ χ`. -/
theorem adjoint_Kgate_v1 (V : UnitaryOp 𝕢) (χ : 𝕢) :
    LinearMap.adjoint (Kgate V) (gv q1 χ) = gv qplus χ := by
  rw [← Kgate_gv V (uRus_vpair_qplus V χ), adjoint_apply_apply (isUnitary_Kgate V)]

/-! ### The initialisation channel — the library's (`Qhl/Register/TwoQubits.lean`
`gKraus`/`dualInit_outerLM`): resetting the ancilla sends `∣u ⊗ v⟩⟨u ⊗ v∣` to
`|⟪0,u⟫|² (∣0 ⊗ v⟩⟨0 ⊗ v∣ + ∣1 ⊗ v⟩⟨1 ⊗ v∣)`. -/

/-! ## §6. The invariant -/

section Invariant

variable (V : UnitaryOp 𝕢) (ψ₀ : 𝕢)

/-- The invariant's effect family: at `succ = 1` the success projector
`∣0 ⊗ Vψ₀⟩⟨0 ⊗ Vψ₀∣`, at `succ = 0` the effect `1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣` written as an
orthogonal sum of two rank-one projectors. -/
noncomputable def Jop (σ : Store) : EndM D (univ : Finset L) :=
  if σ.1 then outerLM (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀))
  else outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀)

variable {ψ₀}

theorem norm_gv_w (hψ₀ : ‖ψ₀‖ = 1) : ‖gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)‖ = 1 :=
  norm_gv norm_q0 (norm_unitaryOp_apply V hψ₀)

/-- The `succ = 0` branch of the invariant is an effect: it is the orthogonal
sum of two rank-one projectors. -/
theorem isEffect_Jop_false (hψ₀ : ‖ψ₀‖ = 1) :
    IsEffect (outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀)) :=
  isEffect_add_outerLM_of_orthonormal (norm_gv_q0 hψ₀) (norm_gv_q1 hψ₀) inner_gv_q0_q1

variable (ψ₀)

/-- **The loop invariant.** -/
noncomputable def J (hψ₀ : ‖ψ₀‖ = 1) : Assn Store D where
  op := Jop V ψ₀
  isEffect σ := by
    rw [Jop]
    by_cases h : σ.1 = true
    · rw [if_pos h]
      exact isEffect_outerLM_self (norm_gv_w V hψ₀)
    · rw [Bool.not_eq_true] at h
      rw [if_neg (by simp [h])]
      exact isEffect_Jop_false hψ₀

@[simp]
theorem J_op (hψ₀ : ‖ψ₀‖ = 1) (σ : Store) : (J V ψ₀ hψ₀).op σ = Jop V ψ₀ σ := rfl

theorem Jop_true {σ : Store} (h : σ.1 = true) :
    Jop V ψ₀ σ = outerLM (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) := by
  rw [Jop, if_pos h]

theorem Jop_false {σ : Store} (h : σ.1 = false) :
    Jop V ψ₀ σ = outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀) := by
  rw [Jop, if_neg (by simp [h])]

end Invariant

/-! ## §7. The backward chain of the body, for the invariant -/

section Chains

variable (V : UnitaryOp 𝕢) {ψ₀ : 𝕢} (hψ₀ : ‖ψ₀‖ = 1)

/-- The precondition the four axioms derive for the invariant. -/
noncomputable def bodyPre : Assn Store D :=
  ((((J V ψ₀ hψ₀).comp setSucc).measurePre rA meas updM).unitaryPre rAT
      (gateAT V)).initPre fun _ => regA.sig

/-- (Ax-Meas): both branches are collected, the `m = 0` one carrying the
success projector and the `m = 1` one the retry projector. -/
theorem measurePre_chain (σ : Store) :
    (((J V ψ₀ hψ₀).comp setSucc).measurePre rA meas updM).op σ
      = outerLM (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀))
        + outerLM (gv q1 ψ₀) (gv q1 ψ₀) := by
  rw [Assn.measurePre_op_of_dist _ rA meas updM (distA σ), Fin.sum_univ_two]
  simp only [regLift_rA, adjoint_Kmeas, Assn.comp_op, J_op, updM_zero, updM_one]
  rw [show setSucc (σ.1, false) = (true, false) from rfl,
    show setSucc (σ.1, true) = (false, true) from rfl,
    Jop_true V ψ₀ rfl, Jop_false V ψ₀ rfl]
  rw [Kmeas_conj_outer, LinearMap.add_comp, LinearMap.comp_add, Kmeas_conj_outer,
    Kmeas_conj_outer, Kmeas_zero_gv_q0, Kmeas_one_gv_q0, Kmeas_one_gv_q1,
    outerLM_zero_left, zero_add]

/-- (Ax-Uni): the rotation block pulls the two projectors back to the
`∣-⟩`/`∣+⟩` ancilla profiles. -/
theorem unitaryPre_chain (σ : Store) :
    ((((J V ψ₀ hψ₀).comp setSucc).measurePre rA meas updM).unitaryPre rAT
        (gateAT V)).op σ
      = outerLM (gv qminus ψ₀) (gv qminus ψ₀) + outerLM (gv qplus ψ₀) (gv qplus ψ₀) := by
  rw [Assn.unitaryPre_op_of_dist _ rAT _ (distAT σ), regLift_rAT, measurePre_chain V hψ₀,
    LinearMap.add_comp, LinearMap.comp_add, adjoint_comp_outerLM_comp,
    adjoint_comp_outerLM_comp, adjoint_Kgate_w, adjoint_Kgate_v1]

/-- (Ax-Init): resetting the ancilla turns the two `∣∓⟩` profiles back into the
`succ = 0` branch of the invariant — each contributes `½`, and they add up
to `1`. -/
theorem bodyPre_op (σ : Store) :
    (bodyPre V hψ₀).op σ
      = outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀) := by
  rw [bodyPre, Assn.initPre_op, unitaryPre_chain V hψ₀, map_add, dualInit_outerLM,
    dualInit_outerLM, inner_q0_qminus, inner_q0_qplus, star_inv_sqrt_two,
    inv_sqrt_two_mul_self, ← add_smul]
  norm_num

/-- **The body triple** `{J ∧ succ = 0} body {J}`: (Ax-Init), (Ax-Uni),
(Ax-Meas), (Ax-Ass) chained by (R-Seq), with one (R-Conseq) at the entry — and
the entry entailment is an *equality* of effects. -/
theorem bodyDeriv : DerivTot ((J V ψ₀ hψ₀).mand guard) (rusBody V) (J V ψ₀ hψ₀) := by
  refine DerivTot.conseq ?_
    (DerivTot.seq (DerivTot.initProg (fun _ => regA.sig) _)
      (DerivTot.seq (DerivTot.unitary rAT (gateAT V) _)
        (DerivTot.seq (DerivTot.measure rA meas updM _)
          (DerivTot.assign setSucc (J V ψ₀ hψ₀)))))
    (Assn.le_refl' _)
  intro σ
  by_cases h : guard σ = true
  · have hσ : σ.1 = false := by simpa [guard] using h
    rw [Assn.mand_op_of_true h, J_op, Jop_false V ψ₀ hσ]
    exact le_of_eq (bodyPre_op V hψ₀ σ).symm
  · rw [Bool.not_eq_true] at h
    exact Assn.op_zero_le (Assn.mand_op_of_false h)

/-! ## §8. The backward chain of the body, for the complement -/

/-- The precondition the four axioms derive for the *complement* of the
guard-masked invariant. -/
noncomputable def complPre : Assn Store D :=
  (((((J V ψ₀ hψ₀).mand guard).compl.comp setSucc).measurePre rA meas updM).unitaryPre rAT
      (gateAT V)).initPre fun _ => regA.sig

theorem measurePre_compl (σ : Store) :
    ((((J V ψ₀ hψ₀).mand guard).compl.comp setSucc).measurePre rA meas updM).op σ
      = 1 - outerLM (gv q1 ψ₀) (gv q1 ψ₀) := by
  rw [Assn.measurePre_op_of_dist _ rA meas updM (distA σ), Fin.sum_univ_two]
  simp only [regLift_rA, adjoint_Kmeas, Assn.comp_op, Assn.compl_op, updM_zero, updM_one]
  rw [show setSucc (σ.1, false) = (true, false) from rfl,
    show setSucc (σ.1, true) = (false, true) from rfl,
    Assn.mand_op_of_false (b := guard) (σ := (true, false)) rfl,
    Assn.mand_op_of_true (b := guard) (σ := (false, true)) rfl,
    J_op, Jop_false V ψ₀ rfl, sub_zero]
  have hsplit : Kmeas 1 ∘ₗ (1 - (outerLM (gv q0 ψ₀) (gv q0 ψ₀)
        + outerLM (gv q1 ψ₀) (gv q1 ψ₀))) ∘ₗ Kmeas 1
      = Kmeas 1 ∘ₗ Kmeas 1
        - (outerLM (Kmeas 1 (gv q0 ψ₀)) (Kmeas 1 (gv q0 ψ₀))
          + outerLM (Kmeas 1 (gv q1 ψ₀)) (Kmeas 1 (gv q1 ψ₀))) := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.add_comp, LinearMap.comp_add,
      Kmeas_conj_outer, Kmeas_conj_outer, Module.End.one_eq_id, LinearMap.id_comp]
  rw [show Kmeas 0 ∘ₗ (1 : EndM D (univ : Finset L)) ∘ₗ Kmeas 0 = Kmeas 0 ∘ₗ Kmeas 0 by
      rw [Module.End.one_eq_id, LinearMap.id_comp], hsplit,
    Kmeas_one_gv_q0, Kmeas_one_gv_q1, outerLM_zero_left, zero_add]
  have hcomp := Kmeas_complete
  rw [adjoint_Kmeas, adjoint_Kmeas] at hcomp
  rw [show Kmeas 0 ∘ₗ Kmeas 0 + (Kmeas 1 ∘ₗ Kmeas 1 - outerLM (gv q1 ψ₀) (gv q1 ψ₀))
      = (Kmeas 0 ∘ₗ Kmeas 0 + Kmeas 1 ∘ₗ Kmeas 1) - outerLM (gv q1 ψ₀) (gv q1 ψ₀) by abel,
    hcomp]

theorem unitaryPre_compl (σ : Store) :
    (((((J V ψ₀ hψ₀).mand guard).compl.comp setSucc).measurePre rA meas updM).unitaryPre rAT
        (gateAT V)).op σ
      = 1 - outerLM (gv qplus ψ₀) (gv qplus ψ₀) := by
  rw [Assn.unitaryPre_op_of_dist _ rAT _ (distAT σ), regLift_rAT, measurePre_compl V hψ₀,
    LinearMap.sub_comp, LinearMap.comp_sub, adjoint_comp_outerLM_comp, adjoint_Kgate_v1,
    Module.End.one_eq_id, LinearMap.id_comp, (isUnitary_Kgate V).1, Module.End.one_eq_id]

/-- **The complement chain**: one pass of the body leaves at most `1 − ½·J` of
the guard-true mass behind — the contraction factor `c = ½` is the success
probability of a single pass. -/
theorem complPre_op (σ : Store) :
    (complPre V hψ₀).op σ
      = 1 - (2⁻¹ : ℂ) • (outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀)) := by
  rw [complPre, Assn.initPre_op, unitaryPre_compl V hψ₀, map_sub, dualInit_outerLM,
    inner_q0_qplus, star_inv_sqrt_two, inv_sqrt_two_mul_self]
  congr 1
  exact IsTP.isUnital_dualSO D (initLift_isQC (D := D) regA.sig).2

theorem complDeriv :
    DerivTot (complPre V hψ₀) (rusBody V) ((J V ψ₀ hψ₀).mand guard).compl :=
  DerivTot.seq (DerivTot.initProg (fun _ => regA.sig) _)
    (DerivTot.seq (DerivTot.unitary rAT (gateAT V) _)
      (DerivTot.seq (DerivTot.measure rA meas updM _)
        (DerivTot.assign setSucc ((J V ψ₀ hψ₀).mand guard).compl)))

/-! ## §9. The contraction premise and the loop -/

/-- The pointwise mass identity behind the contraction: on the guard the
complement precondition's expectation is exactly `tr ρ − ½·⟪J⟫`. -/
theorem expect_complPre (s : CQState Store D) (hb : guard s.cls = true) :
    expect (complPre V hψ₀).op s = (s.q.mass : ℝ) - 2⁻¹ * expect (J V ψ₀ hψ₀).op s := by
  have hσ : s.cls.1 = false := by simpa [guard] using hb
  have hJ : (J V ψ₀ hψ₀).op s.cls
      = outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀) := Jop_false V ψ₀ hσ
  rw [expect, expect, complPre_op V hψ₀, hJ,
    show s.q.op ∘ₗ (1 - (2⁻¹ : ℂ) • (outerLM (gv q0 ψ₀) (gv q0 ψ₀)
          + outerLM (gv q1 ψ₀) (gv q1 ψ₀)))
        = s.q.op - (2⁻¹ : ℂ) • (s.q.op ∘ₗ (outerLM (gv q0 ψ₀) (gv q0 ψ₀)
          + outerLM (gv q1 ψ₀) (gv q1 ψ₀))) from by
      rw [LinearMap.comp_sub, LinearMap.comp_smul, Module.End.one_eq_id, LinearMap.comp_id],
    map_sub, map_smul, Complex.sub_re, ← PDensity.coe_mass]
  simp [Complex.mul_re]
  rfl

/-- **The contraction premise** with `c = ½`: each pass of the body sends at
least half of the guard-true invariant mass out of the loop. Discharged
through the *complement* triple `{complPre} body {(J ∧ b)ᶜ}` by the library
bridge `LoopBodyContraction.of_complement`; the pointwise inequality is in fact
an equality. -/
theorem contraction :
    LoopBodyContraction guard (rusBody V) (J V ψ₀ hψ₀) (2⁻¹ : ℝ≥0) := by
  refine LoopBodyContraction.of_complement (complDeriv V hψ₀).sound fun s hb => ?_
  have he : 0 ≤ expect (J V ψ₀ hψ₀).op s :=
    expect_nonneg (fun σ => (J V ψ₀ hψ₀).isPositive σ) s
  have hc : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (2⁻¹ : ℝ) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    norm_num
  simp only [expectE]
  rw [expect_complPre V hψ₀ s hb, hc, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2⁻¹),
    ← ENNReal.ofReal_coe_nnreal (p := s.q.mass),
    ← ENNReal.ofReal_sub _ (mul_nonneg (by norm_num) he)]

/-- **(R-Loop-ast)**: the loop is totally correct — with probability one it
terminates, in a state satisfying `J ∧ succ = 1`. Not derivable in the ranked
system: the retry branch restores the store exactly, so no ranking function
decreases. -/
theorem loopValid :
    validTot (J V ψ₀ hψ₀) (rusLoop V) ((J V ψ₀ hψ₀).mandNot guard) :=
  validTot_while_ast (2⁻¹ : ℝ≥0) (by norm_num) (bodyDeriv V hψ₀).sound (contraction V hψ₀)

/-! ## §10. The headline triple -/

/-- The precondition: the effect `1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣`, written as the orthogonal sum
of the two rank-one projectors of `∣0⟩ₐ ⊗ ψ₀` and `∣1⟩ₐ ⊗ ψ₀`. It says nothing
about the ancilla (the program resets it) and pins the data wire to `ψ₀`. -/
noncomputable def rusPre : Assn Store D where
  op _ := outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀)
  isEffect _ := isEffect_Jop_false hψ₀

@[simp]
theorem rusPre_op (σ : Store) :
    (rusPre hψ₀).op σ = outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀) := rfl

/-- The postcondition: `succ = 1` **and** the world is in the pure state
`∣0⟩ₐ ⊗ V ψ₀` — the data wire carries the rotated ket. -/
noncomputable def rusPost : Assn Store D :=
  (Assn.ofState (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) (norm_gv_w V hψ₀)).mask fun σ => σ.1 = true

theorem postShape : (J V ψ₀ hψ₀).mandNot guard = rusPost V hψ₀ := by
  refine Assn.ext (funext fun σ => ?_)
  by_cases h : σ.1 = true
  · rw [Assn.mandNot_op_of_false (b := guard) (by simp [guard, h]), J_op, Jop_true V ψ₀ h,
      rusPost, Assn.mask_op_of_pos (φ := fun σ : Store => σ.1 = true) (σ := σ) h,
      Assn.ofState_op]
  · rw [Bool.not_eq_true] at h
    rw [Assn.mandNot_op_of_true (b := guard) (by simp [guard, h]), rusPost,
      Assn.mask_op_of_neg (by simp [h])]

theorem rusPre_le : rusPre hψ₀ ≤ (J V ψ₀ hψ₀).comp initSucc := fun σ =>
  le_of_eq (by rw [Assn.comp_op, J_op, Jop_false V ψ₀ (rfl : (initSucc σ).1 = false), rusPre_op])

/-- **The RUS triple**, for every single-qubit gate `V` and every unit data ket
`ψ₀`:

```
⊨tot {1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣}  succ := 0; while succ = 0 do … od  {succ ∧ ∣0⟩ₐ ⊗ ∣Vψ₀⟩}
```

Semantics: the density-matrix/effect one, so this quantifies over **all** ρ.
Termination is almost sure, not ranked. -/
theorem rusValid : validTot (rusPre hψ₀) (rusProg V) (rusPost V hψ₀) := by
  have hl : validTot (J V ψ₀ hψ₀) (rusLoop V) (rusPost V hψ₀) := by
    rw [← postShape V hψ₀]
    exact loopValid V hψ₀
  exact validTot_seq
    (validTot_conseq (rusPre_le V hψ₀) (DerivTot.assign initSucc (J V ψ₀ hψ₀)).sound
      (Assn.le_refl' _)) hl

/-! ## §11. Non-vacuity -/

/-- A concrete input the precondition accepts with *all* of its mass: the pure
state `∣0⟩ₐ ⊗ ψ₀`. -/
noncomputable def inputState (ψ₀ : 𝕢) : CQState Store D :=
  ⟨(true, false), ⟨outerLM (gv q0 ψ₀) (gv q0 ψ₀), isPositive_outerLM_self _⟩⟩

/-- **The precondition is satisfiable**: it has expectation `1` — the full
mass — in the concrete input state. -/
theorem rusPre_expect_one : expectE (rusPre hψ₀).op (inputState ψ₀) = 1 := by
  have h0 : (⟪gv q0 ψ₀, gv q0 ψ₀⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_gv_q0 hψ₀]; norm_num
  have h1 : (⟪gv q1 ψ₀, gv q0 ψ₀⟫ : ℂ) = 0 := by rw [gv_inner, inner_q1_q0, mul_zero]
  rw [expectE, expect, rusPre_op,
    show (inputState ψ₀).q.op = outerLM (gv q0 ψ₀) (gv q0 ψ₀) from rfl,
    LinearMap.comp_add, map_add, trace_outerLM_comp, trace_outerLM_comp]
  rw [outerLM_apply, outerLM_apply, inner_smul_right, inner_smul_right, h0, h1]
  simp

include hψ₀ in
/-- **The postcondition is a distinct, nonzero pure state**: the data wire
really carries `V ψ₀`. -/
theorem rusPost_ne_zero : gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀) ≠ 0 := by
  intro h
  have := norm_gv_w V hψ₀
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- The postcondition's state is literally the two-wire product `∣0⟩ₐ ⊗ Vψ₀`. -/
theorem rusPost_state :
    gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀) = prodV D (fam q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) := rfl

end Chains

end Qhl.RUS

#print axioms Qhl.RUS.rusValid
#print axioms Qhl.RUS.bodyDeriv
#print axioms Qhl.RUS.complDeriv
#print axioms Qhl.RUS.contraction
#print axioms Qhl.RUS.loopValid
#print axioms Qhl.RUS.postShape
#print axioms Qhl.RUS.rusPre_expect_one
#print axioms Qhl.RUS.rusPost_ne_zero
