import Qhl.Logic.Source.BasicDerived
import Qhl.Logic.Soundness
import Qhl.Gate.Qubit
import Qhl.Register.Qubits
import Qhl.Logic.UnitaryFull
import Qhl.Register.TwoQubits

/-! # The Bell-state triple

The Bell program `q₀ *= H; (q₀,q₁) *= CNOT` over the two-qubit world
`L = Bool`, and its triple in `QHL⁺_tot`:

```
⊢ₜ { ∣00⟩ }  q₀ *= H; (q₀,q₁) *= CNOT  { ∣Φ⁺⟩ },    ∣Φ⁺⟩ = 2^{-1/2}(∣00⟩ + ∣11⟩).
```

The derivation mirrors the program: **two** (Ax-Uni)+(R-Conseq) steps — one
call to the library's pure-state rule `DerivTot.unitary_state` per gate (CoqQ
`AxV_UT`, `qhl.v:1623`) — joined by (R-Seq). The only obligations are the two
action facts `H∣0⟩ ⊗ ∣0⟩ = ∣+⟩ ⊗ ∣0⟩` and `CNOT (∣+⟩ ⊗ ∣0⟩) = ∣Φ⁺⟩`,
discharged by the library bridges: the one-site gate collapse `gateAt_prodV`
(CoqQ `tentf_tuple_apply` under `lift_lf`) and the two-site frame bridge
`regLift_pairGate_prodV` (CoqQ `lift_lf` on a `tenvm` state, the vector form of
`RV_Frame`) fed the gate's own fact `CNOT_vpair`, over the two-wire product
algebra `gv` of `Qhl/Register/TwoQubits.lean`.

The triple is genuine and non-vacuous: the precondition is the unit vector
`∣00⟩` (`ket00_deltav` pins the basis delta), the postcondition the distinct
unit vector `∣Φ⁺⟩` (`bellVec_deltav` pins `2^{-1/2}(∣00⟩ + ∣11⟩)` in delta
form). Both assertions are the projector *effects* `∣v⟩⟨v∣` (`Assn.ofState`) —
kets name rank-1 quantum predicates on density operators — and `bellValid` runs
`bellStateDeriv` through soundness: the expectation of `∣00⟩⟨00∣` in **any**
input density operator bounds the terminal expectation of `∣Φ⁺⟩⟨Φ⁺∣`. -/

namespace Qhl.BellProgram

open Qhl TwoQubits Finset

/-! ## §1. The fixture: two qubit cells, one classical state -/

/-- The world of the example: two cells, labelled `false` and `true`. -/
abbrev L : Type := Bool

/-- Each cell of the world is a qubit: the library's qubit-cell family
(`Qhl/Register/Qubits.lean`) at the two-cell world `L`. -/
abbrev D : L → Type := QubitCells L

/-- The register of the Hadamard step: the cell `false`. -/
def regH : Reg L 1 := Reg.single false

/-- The register of the `CNOT` step: both cells, in the order `false, true`. -/
def regC : Reg L 2 := Reg.pair false true (by decide)

/-- The register *expression* of the Hadamard step (W3); it is constant. -/
def rH : RegExpr Unit L 1 := RegExpr.const regH

/-- The register expression of the `CNOT` step (W3); it is constant. -/
def rC : RegExpr Unit L 2 := RegExpr.const regC

theorem distH (σ : Unit) : Function.Injective (rH σ) := regH.inj

theorem distC (σ : Unit) : Function.Injective (rC σ) := regC.inj

/-- The library Hadamard on the tuple space of a one-cell register (R-2): the
library's one-cell gate `singleGate` at the cell `false`. -/
noncomputable def gateH (σ : Unit) : UnitaryOp (TSpace D (rH σ)) :=
  singleGate D false H

/-- The library `CNOT` on the tuple space of a two-cell register (R-2). -/
noncomputable def gateC (σ : Unit) : UnitaryOp (TSpace D (rC σ)) :=
  euclCongrOp (piFinTwoEquiv fun _ => Bool).symm CNOT

/-- The second statement, `(q₀,q₁) *= CNOT`. -/
noncomputable def cnotStep : Prog Unit D := .unitary 2 rC gateC

/-- E-1: the Bell program `q₀ *= H; (q₀,q₁) *= CNOT`. -/
noncomputable def bellProg : Prog Unit D := .seq (.unitary 1 rH gateH) cnotStep

/-! ## §2. The two states -/

/-- The computational-basis state `∣00⟩`: the library's all-zeros product state
`⊗ᵢ ∣0⟩` at the two-cell world. -/
noncomputable def ket00 : HS D (univ : Finset L) := allZerosOn L

/-- `∣00⟩` in the two-wire product form `gv` of `Qhl/Register/TwoQubits.lean`. -/
theorem ket00_gv : ket00 = gv q0 q0 := by
  change prodV D (fun _ => q0) = prodV D (fam q0 q0)
  exact prodV_congr D fun i _ => by cases i <;> rfl

theorem norm_ket00 : ‖ket00‖ = 1 := norm_allZerosOn L

/-- The Bell state `∣Φ⁺⟩ = 2^{-1/2}(∣00⟩ + ∣11⟩)`, in product form; pinned to
its computational-basis (delta) form by `bellVec_deltav`. -/
noncomputable def bellVec : HS D (univ : Finset L) :=
  (Real.sqrt 2 : ℂ)⁻¹ • (gv q0 q0 + gv q1 q1)

/-! ## §3. The two gate actions -/

/-- The Hadamard step, `∣00⟩ ↦ ∣+0⟩`: the one-site bridge `gateAt_prodV` plus
the atom `H_q0`. -/
theorem KH_ket00 : regLift regH (gateH ()) ket00 = gv qplus q0 := by
  rw [ket00_gv]
  change gateAt L false H (prodV D (fam q0 q0)) = gv qplus q0
  rw [gateAt_prodV, fam_false, H_q0, fam_update_a]
  rfl

/-- The `CNOT` step on basis products, `∣ab⟩ ↦ ∣a (a ⊕ b)⟩`: the two-site frame
bridge `regLift_pairGate_prodV` fed the gate's own fact `CNOT_vpair`. -/
theorem KC_gv (a b : Bool) :
    regLift regC (gateC ()) (gv (qbit a) (qbit b)) = gv (qbit a) (qbit (xor a b)) := by
  have h := regLift_pairGate_prodV false true (by decide) CNOT
    (fam (qbit a) (qbit b)) (CNOT_vpair a b)
  rw [fam_update_both] at h
  exact h

theorem KC_00 : regLift regC (gateC ()) (gv q0 q0) = gv q0 q0 := KC_gv false false

theorem KC_10 : regLift regC (gateC ()) (gv q1 q0) = gv q1 q1 := KC_gv true false

/-- `∣+0⟩` split by linearity of the product in its first factor. -/
theorem gv_qplus_q0 : gv qplus q0 = (Real.sqrt 2 : ℂ)⁻¹ • (gv q0 q0 + gv q1 q0) := by
  rw [← gv_add_left, ← gv_smul_left]
  rfl

/-- **The `CNOT` action**: `CNOT ∣+0⟩ = ∣Φ⁺⟩`, by linearity from `KC_00`/`KC_10`. -/
theorem KC_plus : regLift regC (gateC ()) (gv qplus q0) = bellVec := by
  rw [gv_qplus_q0, map_smul, map_add, KC_00, KC_10]
  rfl

theorem norm_bellVec : ‖bellVec‖ = 1 := by
  rw [← KC_plus]
  exact norm_eq_one_of_isUnitary (isUnitary_regLift regC (gateC ()))
    (norm_gv_qplus norm_q0)

/-! ## §4. The assertions, the derivation, and soundness -/

/-- The assertion "the register is in `∣00⟩`": the projector effect `∣00⟩⟨00∣`. -/
noncomputable def P00 : Assn Unit D := Assn.ofState ket00 norm_ket00

@[simp] theorem P00_op (σ : Unit) : P00.op σ = outerLM ket00 ket00 := rfl

/-- The assertion "the register is in `∣Φ⁺⟩`": the projector effect `∣Φ⁺⟩⟨Φ⁺∣`. -/
noncomputable def Pbell : Assn Unit D := Assn.ofState bellVec norm_bellVec

@[simp] theorem Pbell_op (σ : Unit) : Pbell.op σ = outerLM bellVec bellVec := rfl

/-- **The Bell triple**: `{∣00⟩⟨00∣} q₀ *= H; (q₀,q₁) *= CNOT {∣Φ⁺⟩⟨Φ⁺∣}` is
derivable in `QHL⁺_tot` — one `DerivTot.unitary_state` call per gate (each is
(Ax-Uni)+(R-Conseq), CoqQ `AxV_UT`), joined by (R-Seq). -/
theorem bellStateDeriv : DerivTot P00 bellProg Pbell :=
  DerivTot.seq
    (DerivTot.unitary_state regH (gateH ()) norm_ket00 (norm_gv_qplus norm_q0) KH_ket00)
    (DerivTot.unitary_state regC (gateC ()) (norm_gv_qplus norm_q0) norm_bellVec KC_plus)

/-- **The Bell triple, semantically** — `bellStateDeriv` through soundness: for
**every** input density operator, the expectation of `∣00⟩⟨00∣` bounds the
terminal expectation of `∣Φ⁺⟩⟨Φ⁺∣`. -/
theorem bellValid : validTot P00 bellProg Pbell := bellStateDeriv.sound

/-! ## §5. Non-vacuity: both endpoints pinned to their basis (delta) forms -/

/-- The precondition is literally the basis ket `∣00⟩`. -/
theorem ket00_deltav : ket00 = deltav D fun _ => false := allZerosOn_eq_deltav L

theorem gv_q0_deltav : gv q0 q0 = deltav D fun _ => false :=
  (prodV_congr D fun i _ => by cases i <;> rfl).trans (prodV_single D fun _ => false)

theorem gv_q1_deltav : gv q1 q1 = deltav D fun _ => true :=
  (prodV_congr D fun i _ => by cases i <;> rfl).trans (prodV_single D fun _ => true)

/-- The postcondition is literally `2^{-1/2}(∣00⟩ + ∣11⟩)` — a unit vector
distinct from the precondition, so the triple is genuine in both directions. -/
theorem bellVec_deltav :
    bellVec = (Real.sqrt 2 : ℂ)⁻¹ • (deltav D (fun _ => false) + deltav D (fun _ => true)) := by
  rw [← gv_q0_deltav, ← gv_q1_deltav]
  rfl

end Qhl.BellProgram

#print axioms Qhl.BellProgram.bellStateDeriv
#print axioms Qhl.BellProgram.bellValid

/-! # Bell preparation through the source derivation constructors -/

namespace Qhl.BellProgram

open TwoQubits

/-- The original Bell program and projector predicates, with the paper's
classical condition `True` and everywhere-defined quantum predicates. -/
theorem bellSourceDeriv :
    SourceDerivTot (SourceAssertion.ofAssn P00 (fun _ => True)) bellProg
      (SourceAssertion.ofAssn Pbell (fun _ => True)) :=
  SourceDerivTot.seq
    (SourceDerivTot.unitary_state regH (gateH ()) norm_ket00
      (norm_gv_qplus norm_q0) KH_ket00)
    (SourceDerivTot.unitary_state regC (gateC ()) (norm_gv_qplus norm_q0)
      norm_bellVec KC_plus)

/-- The exact original Bell semantic triple, obtained from its source proof. -/
theorem bellSourceValid : validTot P00 bellProg Pbell := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using bellSourceDeriv.sound

end Qhl.BellProgram

#print axioms Qhl.BellProgram.bellSourceDeriv
#print axioms Qhl.BellProgram.bellSourceValid
