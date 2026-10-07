import Qhl.Logic.AncillaEmbed

/-!
# Guard-masked pure-state families: (Ax-Uni) inside a ranked loop body

Inside the body of a ranked `while` loop the assertions carry the loop's
guard and ranking mask: the invariant `J` enters as `(J.mand b).mask φ`
((R-Loop-tot), `Qhl/Logic/Rules.lean`).  When `J` is a store-indexed family of
pure-state projectors (`Assn.ofStateFam`, `Qhl/Logic/AncillaEmbed.lean`), each
unitary gate of the body advances the state family exactly as it does outside
the loop; the guard and the mask ride along untouched because a unitary step
does not change the classical store.

This file proves that once and for all:

* `Assn.stateFam_guard_unitary_le` — the (Ax-Uni) entailment premise for a
  guard-masked pure-state family (the generic form of the per-gate premises a
  ranked-loop derivation hand-rolls otherwise);
* `DerivTot.unitary_stateFam_guard` — (Ax-Uni)+(R-Conseq) at a guard-masked
  family: one gate, the family evolved by the lifted gate;
* `DerivTot.forProg_unitary_chain_guard` — the straight-line `for`-fold of
  store-computed gates at a guard-masked family: the family evolved by the
  semantic chain operator (`chainOp`), one (Ax-Uni)+(R-Conseq) per gate glued
  by (R-Seq) and closed by (Ax-Ski);
* `Assn.ofStateFam_guard_le` — (R-Conseq) between guard-masked families that
  agree under the guard and the mask.

Everything is built from the `DerivTot` constructors `.skip`, `.seq`,
`.unitary`, `.conseq` alone — no new rule primitive, no semantic argument.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-- A gate list fixes any vector each of its gates fixes. -/
theorem chainOp_fix {ι : Type*} (li : List ι) (K : ι → EndM D (univ : Finset L))
    {z : HS D (univ : Finset L)} (h : ∀ i, K i z = z) : chainOp li K z = z := by
  induction li with
  | nil => rfl
  | cons i t ih => rw [chainOp_apply_cons, h i, ih]

/-- Guard-masked pure-state families entail each other when the underlying
state families agree wherever the guard holds and the mask is on. -/
theorem Assn.ofStateFam_guard_le {v w : σT → HS D (univ : Finset L)}
    {hv : ∀ σ, ‖v σ‖ = 1} {hw : ∀ σ, ‖w σ‖ = 1} (b : σT → Bool) (φ : σT → Prop)
    (h : ∀ σ, b σ = true → φ σ → v σ = w σ) :
    ((Assn.ofStateFam (σT := σT) v hv).mand b).mask φ
      ≤ ((Assn.ofStateFam (σT := σT) w hw).mand b).mask φ := by
  intro σ
  by_cases hφ : φ σ
  · by_cases hb : b σ = true
    · refine le_of_eq ?_
      rw [Assn.mask_op_of_pos (A := (Assn.ofStateFam v hv).mand b) hφ,
        Assn.mask_op_of_pos (A := (Assn.ofStateFam w hw).mand b) hφ,
        Assn.mand_op_of_true (A := Assn.ofStateFam v hv) hb,
        Assn.mand_op_of_true (A := Assn.ofStateFam w hw) hb,
        Assn.ofStateFam_op, Assn.ofStateFam_op, h σ hb hφ]
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := (Assn.ofStateFam v hv).mand b) hφ]
      exact Assn.mand_op_of_false (A := Assn.ofStateFam v hv) (by simpa using hb)
  · exact Assn.op_zero_le
      (Assn.mask_op_of_neg (A := (Assn.ofStateFam v hv).mand b) hφ)

/-- **The (Ax-Uni) premise at a guard-masked pure-state family**: whenever the
guard holds and the mask is on, the lifted gate carries `v σ` to `w σ`, so the
masked family of `v` entails the `unitaryPre` transformer of the masked family
of `w`.  Off the guard or off the mask both sides read `0`. -/
theorem Assn.stateFam_guard_unitary_le {k : ℕ} (r : Reg L k)
    (U : σT → UnitaryOp (TSpace D r.toFun))
    {v w : σT → HS D (univ : Finset L)} (hv : ∀ σ, ‖v σ‖ = 1) (hw : ∀ σ, ‖w σ‖ = 1)
    (b : σT → Bool) (φ : σT → Prop)
    (hU : ∀ σ, b σ = true → φ σ →
      regLift r ((U σ : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)) (v σ) = w σ) :
    ((Assn.ofStateFam (σT := σT) v hv).mand b).mask φ
      ≤ ((((Assn.ofStateFam (σT := σT) w hw).mand b).mask φ).unitaryPre
          (RegExpr.const r) U) := by
  intro σ
  by_cases hφ : φ σ
  · by_cases hb : b σ = true
    · refine le_of_eq (Eq.symm (Eq.trans
        (Assn.unitaryPre_op_of_dist _ _ _ (σ := σ) r.inj) ?_))
      rw [Assn.mask_op_of_pos (A := (Assn.ofStateFam w hw).mand b) hφ,
        Assn.mand_op_of_true (A := Assn.ofStateFam w hw) hb,
        Assn.mask_op_of_pos (A := (Assn.ofStateFam v hv).mand b) hφ,
        Assn.mand_op_of_true (A := Assn.ofStateFam v hv) hb,
        Assn.ofStateFam_op, Assn.ofStateFam_op]
      exact adjoint_conj_outerLM_state r (U σ) (hU σ hb hφ)
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := (Assn.ofStateFam v hv).mand b) hφ]
      exact Assn.mand_op_of_false (A := Assn.ofStateFam v hv) (by simpa using hb)
  · exact Assn.op_zero_le
      (Assn.mask_op_of_neg (A := (Assn.ofStateFam v hv).mand b) hφ)

/-- **(Ax-Uni) at a guard-masked pure-state family, store-computed gate**:

```
⊢ₜ {((|v σ⟩⟨v σ| ∧ b) ∧ φ)}  q̄ *= U(σ)  {((|w σ⟩⟨w σ| ∧ b) ∧ φ)}
```

given `∀ σ, b σ → φ σ → regLift r (U σ) (v σ) = w σ`.  Built from `.unitary`
and `.conseq` alone. -/
theorem DerivTot.unitary_stateFam_guard {k : ℕ} (r : Reg L k)
    (U : σT → UnitaryOp (TSpace D r.toFun))
    {v w : σT → HS D (univ : Finset L)} (hv : ∀ σ, ‖v σ‖ = 1) (hw : ∀ σ, ‖w σ‖ = 1)
    (b : σT → Bool) (φ : σT → Prop)
    (hU : ∀ σ, b σ = true → φ σ →
      regLift r ((U σ : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)) (v σ) = w σ) :
    DerivTot (σT := σT) (((Assn.ofStateFam v hv).mand b).mask φ)
      (.unitary k (RegExpr.const r) U)
      (((Assn.ofStateFam w hw).mand b).mask φ) :=
  DerivTot.conseq (Assn.stateFam_guard_unitary_le r U hv hw b φ hU)
    (DerivTot.unitary (RegExpr.const r) U _) (Assn.le_refl' _)

/-- **A `for`-fold of store-computed unitary gates at a guard-masked
pure-state family**: the postcondition is the family evolved by the semantic
chain operator, the guard and the mask untouched.  One (Ax-Uni)+(R-Conseq)
per gate, glued by (R-Seq) and closed by (Ax-Ski). -/
theorem DerivTot.forProg_unitary_chain_guard {ι : Type*} (l : List ι) (k : ι → ℕ)
    (r : ∀ i, Reg L (k i)) (U : ∀ i, σT → UnitaryOp (TSpace D (r i).toFun))
    (v : σT → HS D (univ : Finset L)) (hv : ∀ σ, ‖v σ‖ = 1)
    (b : σT → Bool) (φ : σT → Prop) :
    DerivTot (σT := σT) (((Assn.ofStateFam v hv).mand b).mask φ)
      (Qhl.forProg l fun i => Prog.unitary (k i) (RegExpr.const (r i)) (U i))
      (((Assn.ofStateFam
          (fun σ => chainOp l
            (fun i => regLift (r i)
              ((U i σ : TSpace D (r i).toFun →ₗ[ℂ] TSpace D (r i).toFun)))
            (v σ))
          (fun σ => norm_eq_one_of_isUnitary
            (isUnitary_chainOp l _ fun _ => isUnitary_regLift _ _) (hv σ))).mand
          b).mask φ) := by
  induction l generalizing v with
  | nil => exact DerivTot.skip _
  | cons i t ih =>
      exact DerivTot.seq
        (DerivTot.unitary_stateFam_guard (r i) (U i) hv
          (fun σ => norm_eq_one_of_isUnitary (isUnitary_regLift _ _) (hv σ))
          b φ (fun σ _ _ => rfl))
        (ih (fun σ => regLift (r i)
            ((U i σ : TSpace D (r i).toFun →ₗ[ℂ] TSpace D (r i).toFun)) (v σ))
          (fun σ => norm_eq_one_of_isUnitary (isUnitary_regLift _ _) (hv σ)))

/-- `DerivTot.forProg_unitary_chain_guard` with a **named** output family: the
postcondition family `w` is supplied by the caller together with the pointwise
chain law `chainOp … (v σ) = w σ` (under the guard and the mask), so a use
site never has to match the `chainOp` display form.  One (R-Conseq) on top of
the chain rule. -/
theorem DerivTot.forProg_unitary_chain_guard' {ι : Type*} (l : List ι) (k : ι → ℕ)
    (r : ∀ i, Reg L (k i)) (U : ∀ i, σT → UnitaryOp (TSpace D (r i).toFun))
    (v : σT → HS D (univ : Finset L)) (hv : ∀ σ, ‖v σ‖ = 1)
    (w : σT → HS D (univ : Finset L)) (hw : ∀ σ, ‖w σ‖ = 1)
    (b : σT → Bool) (φ : σT → Prop)
    (hchain : ∀ σ, b σ = true → φ σ →
      chainOp l
        (fun i => regLift (r i)
          ((U i σ : TSpace D (r i).toFun →ₗ[ℂ] TSpace D (r i).toFun)))
        (v σ) = w σ) :
    DerivTot (σT := σT) (((Assn.ofStateFam v hv).mand b).mask φ)
      (Qhl.forProg l fun i => Prog.unitary (k i) (RegExpr.const (r i)) (U i))
      (((Assn.ofStateFam w hw).mand b).mask φ) :=
  DerivTot.conseq (Assn.le_refl' _)
    (DerivTot.forProg_unitary_chain_guard l k r U v hv b φ)
    (Assn.ofStateFam_guard_le b φ hchain)

end Qhl
