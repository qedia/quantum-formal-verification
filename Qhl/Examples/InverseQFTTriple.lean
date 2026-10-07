import Qhl.Examples.QFTTriple
import Qhl.Logic.UnitaryFull
import Qhl.Logic.Soundness
import Qhl.Register.Fourier

/-! # The inverse quantum Fourier transform: the reversed circuit, verified

For every width `n ≥ 1` and **every** computational-basis input `x`,

```
⊨ₜ { fourierState n x }  iqftRevCir n  { ∣x⟩ },
```

where `iqftRevCir n` is the **genuine inverse-QFT circuit**: the exact adjoint
of the verified QFT circuit `qftCir n` (`Qhl/Examples/QFTTriple.lean`), gate by
gate — the reversal swap network first (`SWAP` is self-inverse), then the
stages in reversed order, each stage its controlled-phase ladder with
**inverted phases** `cR(−2π/2^(j+2))` in reversed rung order followed by its
Hadamard (`H` is self-inverse). Every loop is a genuine counted `while`
(`countedProg`), discharged through `Qhl/Logic/CountedProdChain.lean` — printed
constructors only: (Ax-Ass), (R-Seq), (R-Conseq), (R-Loop-tot) with the
integer variant. The store is `σT = ℕ × ℕ` exactly as in the QFT file; the
reversed stage loop's ladder bound is read **off the store**: the stage at
counter `k'` undoes original stage `n − 1 − k'`, whose ladder has `k'` rungs —
so the inner bound is literally `σ.1`.

The loop invariants are the QFT's own families traversed **backwards**
(`Qhl/Register/Fourier.lean` §9c): the reversal loop runs `qftRevFam` from the
mirrored Fourier profile to the stage-complete profile (`iqftRevFamN`), each
ladder runs `qftLadderFamN` at a *decreasing* rung index
(`qftLadderFamN_step_rev`), and each Hadamard undoes the mid-stage family
(`qftStageMidN_step_H`, from `H_phaseKet_bit`).

**The circuit agrees with the library operator.** §7 assembles the ordered
composite `iqftRevCirOp` of the circuit's own gates (`chainOp`,
`Qhl/Logic/WpChain.lean`) and proves `iqftRevCirOp n = iqftOp n = (qftOp n)†`
by basis agreement — so the reversed circuit really implements the adjoint
Fourier operator on **every** input, superposed or not.

## §1 retains the operator-level form (CoqQ's shape)

CoqQ never builds an IQFT circuit: `IQFT n := (QFT n)^A` (`qtype.v:674`) is the
**operator adjoint**, applied inside QPE as one register-wide gate
`[ut x := IQFT]` (`example.v:1005`) with the action lemma `IQFTEt`. §1 keeps
that layer verbatim — the one-gate program `iqftCir` and its triple
`iqftDeriv`/`iqftValid` — as the **reusable library-operator fact**; it is
*not* an independent circuit verification (the whole content sits in the
operator `iqftOp`). The independent case study is the reversed circuit of
§2–§6. `Qhl/Examples/QPETriple.lean` consumes `iqftRevDeriv` directly for its
readout: the derived store-transport and register-frame rules place the
verified circuit inside QPE while preserving its target eigenstate. The
**circuit-certified** operator action `iqftOp_prodV_phaseKet_of_circuit` (§7)
remains available to clients that use the operator form.

| here | source |
|---|---|
| `iqftOp` (library) | CoqQ `IQFT n := (QFT n)^A` (`qtype.v:674`) |
| `iqftCir` / `iqftDeriv` (§1) | CoqQ `[ut x := IQFT]` (`example.v:1005`) / `IQFTEt` |
| `iqftRevCir` / `iqftRevDeriv` (§2–§6) | the QFT circuit run backwards (adjoint gate sequence) |

The triple is genuine and non-vacuous in both directions: the precondition is
the genuine DFT state `fourierState n x` (CoqQ `QFTbv`), a unit vector
(`norm_fourierState`); the postcondition is literally the computational basis
state `∣x⟩` (`prodV_qbit_eq_deltav`), a distinct unit vector. Both assertions
are the projector effects `|ψ⟩⟨ψ|` (`Assn.ofState`), and the `validTot` finals
quantify over **all** density operators through `DerivTot.sound` — the
density-matrix semantics is untouched. -/

namespace Qhl.InverseQFTTriple

open Finset
open Qhl.QFTTriple

/-! ## §1. The operator-level form (CoqQ `[ut x := IQFT]`)

One register-wide gate carrying the library operator `iqftOp n`; its triple's
only obligation is the action lemma `iqftOp_fourierState` (CoqQ `IQFTEt`).
**This is a library-operator check, not a circuit verification** — the
verified inverse-QFT *circuit* is §2–§6 below, and QPE's readout consumes the
circuit-certified action of §7. -/

/-- The full `n`-qubit register: the identity enumeration of the wires. CoqQ's
whole-system register `x` in `[ut x := IQFT]`. -/
noncomputable def fullReg (n : ℕ) : Reg (QubitL n) n := Reg.ofEquiv (Equiv.refl (Fin n))

/-- The full register covers the whole world. -/
theorem sig_fullReg (n : ℕ) : (fullReg n).sig = (univ : Finset (QubitL n)) :=
  Reg.sig_ofEquiv _

/-- **CoqQ `[ut x := IQFT]`** (`example.v:1005`): the inverse QFT applied as a
single register-wide unitary gate — one program constructor, no loop. The
shape QPE consumes; not an independent circuit. -/
noncomputable def iqftCir (n : ℕ) : Prog Unit (QubitD n) :=
  Prog.unitaryAll (fullReg n) (sig_fullReg n) (iqftOp n)

/-- **The operator-form derivation** — the counterpart of CoqQ's use of
`IQFTEt` inside QPE: **one** call to the library's whole-register (Ax-Uni)
rule `DerivTot.unitaryAll_state`; the only obligation is the action lemma
`iqftOp_fourierState` (derived from the unitarity of `qftOp`), read back into
product form by `prodV_single`. -/
theorem iqftDeriv (n : ℕ) (x : Fin n → Bool) :
    DerivTot (σT := Unit)
      (Assn.ofState (fourierState n x) (norm_fourierState n x))
      (iqftCir n)
      (Assn.ofState (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (fun i => qbit (x i))) (norm_prodV_eq_one _ fun _ => norm_qbit _)) :=
  DerivTot.unitaryAll_state (fullReg n) (sig_fullReg n) (iqftOp n) _ _
    (by rw [iqftOp_fourierState]
        exact (prodV_single (QubitD n) (fun i => x i)).symm)

/-- The operator-form triple, semantically — `iqftDeriv` through soundness. -/
theorem iqftValid (n : ℕ) (x : Fin n → Bool) :
    validTot (σT := Unit)
      (Assn.ofState (fourierState n x) (norm_fourierState n x))
      (iqftCir n)
      (Assn.ofState (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (fun i => qbit (x i))) (norm_prodV_eq_one _ fun _ => norm_qbit _)) :=
  (iqftDeriv n x).sound

/-- **Non-vacuity of the postcondition**: it is literally the computational
basis state `∣x⟩` (CoqQ `t2tv_tuple`). Together with `norm_fourierState` — the
precondition is a unit vector, hence not the zero assertion — the triples of
this file are genuine in both directions. -/
theorem prodV_qbit_eq_deltav (n : ℕ) (x : Fin n → Bool) :
    prodV (QubitD n) (W := (univ : Finset (QubitL n))) (fun i => qbit (x i))
      = deltav (QubitD n) (fun i : ↥(univ : Finset (QubitL n)) => x (i : QubitL n)) :=
  prodV_single (QubitD n) (fun i => x i)

/-! ## §2. The reversed circuit: registers and gates

The store is `σT = ℕ × ℕ`: `σ.1` the (reversed) stage counter — reused first
by the swap loop — and `σ.2` the (reversed) rung counter. The stage at counter
`k'` undoes original QFT stage `k = n − 1 − k'`; its ladder pass `j'` undoes
original rung `j = k' − 1 − j'`, so the touched cells are `cell (n − 1 − σ.1)`
(the stage head) and `cell (n − 1 − σ.2)` (the rung target `k + 1 + j`). -/

section

variable (n : ℕ) [NeZero n]

/-- The stage-head cell of the reversed run: cell `n − 1 − σ.1` — original
stage `k = n − 1 − k'`. -/
def ictrl (σ : ℕ × ℕ) : QubitL n := cell n (n - 1 - σ.1)

/-- The rung-target cell of the reversed ladder: cell `n − 1 − σ.2` — the
original target `k + 1 + j` at `j = k' − 1 − j'`. -/
def itgt (σ : ℕ × ℕ) : QubitL n := cell n (n - 1 - σ.2)

/-- The one-cell register expression of the reversed Hadamard step. -/
def ihReg : RegExpr (ℕ × ℕ) (QubitL n) 1 := fun σ => (Reg.single (ictrl n σ)).toFun

/-- The Hadamard on the tuple space of the one-cell register (`H` is its own
adjoint, so the reversed circuit applies `H` itself). -/
noncomputable def ihGate (σ : ℕ × ℕ) : UnitaryOp (TSpace (QubitD n) (ihReg n σ)) :=
  singleGate (QubitD n) (ictrl n σ) H

/-- The two-cell register expression of a reversed ladder rung. -/
def iladReg : RegExpr (ℕ × ℕ) (QubitL n) 2 := fun σ => ![ictrl n σ, itgt n σ]

/-- The **inverted** controlled phase `cR(−2π/2^(j+2))` of the reversed rung
`j = σ.1 − 1 − σ.2` — the adjoint of the QFT's `cR(2π/2^(j+2))`; `1` where the
register expression degenerates (off the loop masks only). -/
noncomputable def iladGate (σ : ℕ × ℕ) : UnitaryOp (TSpace (QubitD n) (iladReg n σ)) :=
  if h : ictrl n σ ≠ itgt n σ then
    pairGate (ictrl n σ) (itgt n σ) h
      (cphase (-(2 * Real.pi / 2 ^ (σ.1 - 1 - σ.2 + 2))))
  else 1

/-! ## §3. The programs

The swap block of the adjoint circuit is **the same block** as `qftCir`'s —
its transpositions are pairwise disjoint and each is self-inverse, so the
reversed-order product equals the program `revCirc n`, which is reused
verbatim. The stage loops run in reversed order with inverted phases. -/

/-- The reversed controlled-phase ladder of the stage at counter `σ.1`: `σ.1`
rungs (original stage `n − 1 − σ.1` has `n − 1 − (n − 1 − σ.1) = σ.1` of
them), the bound read **off the store**. -/
noncomputable def iqftSub : Prog (ℕ × ℕ) (QubitD n) :=
  countedProg (.snd ℕ) (fun σ => σ.1)
    (.unitary 2 (iladReg n) (iladGate n))

/-- The reversed stage loop: each pass is the inverted ladder of the stage,
**then** its Hadamard — the exact adjoint of `qftIter`'s `H ; ladder` body,
with the stages visited in reversed order. -/
noncomputable def iqftIter : Prog (ℕ × ℕ) (QubitD n) :=
  countedProg (.fst ℕ) (fun _ => n)
    ((iqftSub n).seq (Prog.unitary 1 (ihReg n) (ihGate n)))

/-- **The inverse-QFT circuit**: the reversal swap network first (reused from
`qftCir`), then the reversed stage loop — gate for gate the adjoint of
`qftCir n`. -/
noncomputable def iqftRevCir : Prog (ℕ × ℕ) (QubitD n) := (revCirc n).seq (iqftIter n)

/-! ## §4. The mask arithmetic and the assertion families -/

theorem ictrl_ne_itgt {σ : ℕ × ℕ} (hk : σ.1 < n) (hj : σ.2 < σ.1) :
    ictrl n σ ≠ itgt n σ :=
  cell_ne n (by omega) (by omega) (by omega)

variable (x : Fin n → Bool)

/-- Backward reversal invariant (§9c library family `iqftRevFamN`), as a
store-constant assertion. -/
noncomputable def backAssn (m : ℕ) : Assn (ℕ × ℕ) (QubitD n) :=
  Assn.ofState (prodV (QubitD n) (W := (univ : Finset (QubitL n))) (iqftRevFamN n x m))
    (norm_prodV_eq_one _ (norm_iqftRevFamN n x m))

/-! ## §5. The three loop derivations — printed rules only -/

/-- **The backward reversal loop**: `revCirc` takes the mirrored Fourier
profile back to the stage-complete profile. One `DerivTot.countedProdChainSource`
along `iqftRevFamN`; each swap is one `DerivTot.countedRung_pair_fam` over
`SWAP_vpair`, with a separate identity-predicate gate derivation. The
program and gates are the QFT's closing loop, along the backward family. -/
theorem revCircBack_deriv :
    DerivTot (backAssn n x 0) (revCirc n)
      ((backAssn n x (n / 2)).mask fun σ => σ.1 = n / 2) := by
  refine DerivTot.countedProdChainSource (CounterLens.fst ℕ)
    (hψ₀ := norm_iqftRevFamN n x 0) (hψ₁ := norm_iqftRevFamN n x (n / 2))
    (iqftRevFamN n x) (norm_iqftRevFamN n x) rfl rfl ?_ ?_
  · rw [Assn.ofFam_prodA, Assn.ofFam_prodA]
    exact DerivTot.countedRung_pair_fam (swapReg n) (swapGate n) (ctrl n) (mir n)
      (fun σ hσ => ctrl_ne_mir n hσ)
      (fun _ => SWAP)
      (fun σ => norm_iqftRevFamN n x σ.1) (fun σ => norm_iqftRevFamN n x (σ.1 + 1))
      (fun σ hσ => by
        have hne : ctrl n σ ≠ mir n σ := ctrl_ne_mir n (by omega)
        refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
        rw [show swapGate n σ = pairGate (ctrl n σ) (mir n σ) hne SWAP from by
          simp only [swapGate]; rw [dif_pos hne]]
        rfl)
      (fun σ hσ => by
        have hk : σ.1 < n / 2 := hσ
        have hc : ctrl n σ = cell n σ.1 := rfl
        have hm : mir n σ = cell n (n - 1 - σ.1) := rfl
        exact ⟨phaseKet (qftAngle x σ.1), phaseKet (qftAngle x (n - 1 - σ.1)),
          by rw [hc, hm, iqftRevFamN_left n x hk, iqftRevFamN_right n x hk, SWAP_vpair],
          by rw [hc, hm]; exact iqftRevFamN_step n x hk⟩)
  · intro k
    exact DerivTot.unitary_identityMask (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (ctrl_ne_mir n (by
        change σ.1 = k ∧ k < n / 2 at hσ; omega))).inj

/-- The inverse controlled-phase gate advances the decreasing ladder family. -/
private theorem iladder_action (σ : ℕ × ℕ) (hk : σ.1 < n) (hj : σ.2 < σ.1) :
    ∃ hinj : Function.Injective (iladReg n σ),
      regLift ⟨iladReg n σ, hinj⟩ (iladGate n σ)
        (prodV (QubitD n) (W := univ)
          (qftLadderFamN n x (n - 1 - σ.1) (σ.1 - σ.2))) =
        prodV (QubitD n) (W := univ)
          (qftLadderFamN n x (n - 1 - σ.1) (σ.1 - (σ.2 + 1))) := by
  have hne : ictrl n σ ≠ itgt n σ :=
    ictrl_ne_itgt n hk hj
  refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
  rw [show regLift ⟨iladReg n σ, (Reg.pair _ _ hne).inj⟩ (iladGate n σ)
      = regLift (D := QubitD n) (Reg.pair (ictrl n σ) (itgt n σ) hne)
          (pairGate (D := QubitD n) (ictrl n σ) (itgt n σ) hne
            (cphase (-(2 * Real.pi / 2 ^ (σ.1 - 1 - σ.2 + 2))))) from by
    rw [show iladGate n σ = pairGate (ictrl n σ) (itgt n σ) hne
        (cphase (-(2 * Real.pi / 2 ^ (σ.1 - 1 - σ.2 + 2)))) from by
      simp only [iladGate]; rw [dif_pos hne]]
    rfl]
  exact regLift_cphase_neg_qftLadderFamN n x hk hj hne

/-- The inverse ladder at the current stage, preserving an arbitrary classical frame. -/
theorem iqftSub_current {φ : (ℕ × ℕ) → Prop}
    (hφ : ∀ σ v, φ (σ.1, v) ↔ φ σ) (hk : ∀ σ, φ σ → σ.1 < n) :
    DerivTot ((Assn.ofFam (fun σ => n - σ.1)
      (fun m => prodA (QubitD n) (qftStageFam n x m) (norm_qftStageFam n x m))).mask φ) (iqftSub n)
      ((Assn.ofFam (fun σ => n - 1 - σ.1)
        (fun m => prodA (QubitD n) (qftStageMidN n x m) (norm_qftStageMidN n x m))).mask φ) := by
  have h : DerivTot
      ((Assn.ofStateFam (fun σ : ℕ × ℕ =>
        prodV (QubitD n) (W := univ) (qftStageFam n x (n - σ.1)))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n x (n - σ.1)))).mask φ) (iqftSub n)
      ((Assn.ofStateFam (fun σ : ℕ × ℕ =>
        prodV (QubitD n) (W := univ) (qftStageMidN n x (n - 1 - σ.1)))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageMidN n x (n - 1 - σ.1)))).mask φ) := by
    refine DerivTot.countedStateChainVarSource (CounterLens.snd ℕ) hφ (fun _ _ => rfl)
      (fun m σ => prodV (QubitD n) (W := univ)
        (qftLadderFamN n x (n - 1 - σ.1) (σ.1 - m)))
      (fun m σ => norm_prodV_eq_one _
        (norm_qftLadderFamN n x (n - 1 - σ.1) (σ.1 - m)))
      (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
    · intro σ hσ
      apply congrArg
      have hlt := hk σ hσ
      calc
        qftLadderFamN n x (n - 1 - σ.1) (σ.1 - 0) =
            qftLadderFamN n x (n - 1 - σ.1) (n - 1 - (n - 1 - σ.1)) := by
          congr 1
          omega
        _ = qftStageFam n x ((n - 1 - σ.1) + 1) :=
          qftLadderFamN_full n x (by omega)
        _ = qftStageFam n x (n - σ.1) := by congr 1; omega
    · intro σ _
      rw [Nat.sub_self]
      exact congrArg _ (qftLadderFamN_zero n x (n - 1 - σ.1))
    · exact DerivTot.countedRung_fam (iladReg n) (iladGate n) _ _
        fun σ hσ => iladder_action n x σ (hk σ hσ.1) hσ.2
    · intro z
      exact DerivTot.unitary_identityMask (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (ictrl_ne_itgt n (hk σ hσ.1) hσ.2.1)).inj
  exact DerivTot.conseq
    (Assn.mask_le_mask (fun _ hσ => hσ) (fun σ _ => le_of_eq (by
      rw [Assn.ofFam_op, prodA_op, Assn.ofStateFam_op]))) h
    (Assn.mask_le_mask (fun _ hσ => hσ) (fun σ _ => le_of_eq (by
      rw [Assn.ofFam_op, prodA_op, Assn.ofStateFam_op])))

theorem iqftSub_deriv (k' : ℕ) :
    DerivTot ((stageAssn n x (n - k')).mask fun σ => σ.1 = k' ∧ k' < n) (iqftSub n)
      ((midAssn n x (n - 1 - k')).mask fun σ => σ.1 = k' ∧ k' < n) := by
  refine DerivTot.conseq
    (Assn.mask_le_mask (fun _ h => h) (fun σ hσ => le_of_eq ?_))
    (iqftSub_current n x (fun _ _ => Iff.rfl) (fun σ hσ => by omega))
    (Assn.mask_le_mask (fun _ h => h) (fun σ hσ => le_of_eq ?_))
  · rw [Assn.ofFam_op, hσ.1, prodA_op, stageAssn, Assn.ofState_op]
  · rw [Assn.ofFam_op, hσ.1, prodA_op, midAssn, Assn.ofState_op]

/-- **The reversed stage loop**: from the stage-complete profile back to
`∣x⟩`. One `DerivTot.countedProdChainSource` on the stage counter along
`qftStageFam` at the decreasing index uses `iqftSub_current` and the backward
Hadamard action `qftStageMidN_step_H` for preservation. A separate source
identity derivation establishes decrease independently of this state family. -/
theorem iqftIter_deriv :
    DerivTot (stageAssn n x n) (iqftIter n)
      ((stageAssn n x 0).mask fun σ => σ.1 = n) := by
  refine DerivTot.countedProdChainSource (CounterLens.fst ℕ)
    (hψ₀ := norm_qftStageFam n x n) (hψ₁ := norm_qftStageFam n x 0)
    (fun k' => qftStageFam n x (n - k')) (fun k' => norm_qftStageFam n x (n - k'))
    rfl (by rw [Nat.sub_self]) ?_ ?_
  · have hs := iqftSub_current n x (φ := fun σ => σ.1 < n)
      (fun _ _ => Iff.rfl) (fun _ h => h)
    rw [Assn.ofFam_prodA, Assn.ofFam_prodA] at hs
    rw [Assn.ofFam_prodA, Assn.ofFam_prodA]
    refine DerivTot.seq hs ?_
    exact DerivTot.countedRung_single_fam (ihReg n) (ihGate n) (ictrl n) (fun _ => H)
      (fun σ => norm_qftStageMidN n x (n - 1 - σ.1))
      (fun σ => norm_qftStageFam n x (n - (σ.1 + 1)))
      (fun σ _ => ⟨(Reg.single (ictrl n σ)).inj, rfl⟩)
      (fun σ hσ => by
        change Function.update _ (cell n (n - 1 - σ.1)) _ = _
        rw [show n - (σ.1 + 1) = n - 1 - σ.1 from by omega]
        exact qftStageMidN_step_H n x (by omega))
  · intro k
    refine DerivTot.seq ?_
      (DerivTot.unitary_identityMask (ihReg n) (ihGate n) _
        (fun σ _ => (Reg.single (ictrl n σ)).inj))
    exact DerivTot.countedIdentityVarSource (CounterLens.snd ℕ)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
      (DerivTot.unitary_identityMask (iladReg n) (iladGate n) _
        (fun σ hσ => (Reg.pair _ _ (ictrl_ne_itgt n (by
          have h := hσ.1; change σ.1 = k ∧ k < n at h; omega) hσ.2)).inj))
      (fun z => DerivTot.unitary_identityMask (iladReg n) (iladGate n) _
        (fun σ hσ => (Reg.pair _ _ (ictrl_ne_itgt n (by
          have h := hσ.1; change σ.1 = k ∧ k < n at h; omega) hσ.2.1)).inj))

/-! ## §6. The inverse-QFT triple -/

/-- **The inverse-QFT circuit derivation.** For every width `n ≥ 1` and every
computational-basis input `x`,

```
⊢ₜ { fourierState n x }  iqftRevCir n  { ∣x⟩ }
```

over the store `σT = ℕ × ℕ` at an arbitrary initial store: (R-Seq) of
`revCircBack_deriv` and `iqftIter_deriv`, with (R-Conseq) identifying the
endpoint states — the Fourier state with the mirrored profile
(`fourierState_eq_prodV`), the swap loop's exit with the stage-complete
profile (`iqftRevFamN_half` = `qftStageFam_full`), and the stage loop's exit
with `∣x⟩` (`qftStageFam_zero`). -/
theorem iqftRevDeriv :
    DerivTot (σT := ℕ × ℕ)
      (Assn.ofState (fourierState n x) (norm_fourierState n x))
      (iqftRevCir n)
      (Assn.ofState (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (fun i => qbit (x i))) (norm_prodV_eq_one _ fun _ => norm_qbit _)) :=
  DerivTot.seq
    (DerivTot.conseq
      (Assn.ofState_le_ofState
        ((fourierState_eq_prodV n x).trans (congrArg _ (iqftRevFamN_zero n x).symm)))
      (revCircBack_deriv n x)
      (Assn.mask_le_of_imp_le fun σ _ => le_of_eq (by
        simp only [backAssn, stageAssn, Assn.ofState_op, iqftRevFamN_half,
          qftStageFam_full])))
    (DerivTot.conseq (Assn.le_refl' _) (iqftIter_deriv n x)
      (Assn.mask_le_of_imp_le fun σ _ => le_of_eq (by
        simp only [stageAssn, Assn.ofState_op, qftStageFam_zero])))

/-- **The inverse-QFT triple, semantically** — `iqftRevDeriv` through
soundness: the expectation of the Fourier-state projector in **any** density
operator bounds the terminal expectation of `|x⟩⟨x|`. -/
theorem iqftRevValid :
    validTot (σT := ℕ × ℕ)
      (Assn.ofState (fourierState n x) (norm_fourierState n x))
      (iqftRevCir n)
      (Assn.ofState (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (fun i => qbit (x i))) (norm_prodV_eq_one _ fun _ => norm_qbit _)) :=
  (iqftRevDeriv n x).sound

end

/-! ## §7. The composite operator of the reversed circuit

As for the QFT (`Qhl/Examples/QFTTriple.lean` §9), the circuit's gate sequence
assembles into an operator, and basis agreement identifies it with the library
operator: `iqftRevCirOp n = iqftOp n = (qftOp n)†`. The swap block reuses the
QFT file's `passOpSwap`/`revCircOp` — the reversed circuit applies literally
the same reversal gates. -/

section

variable (n : ℕ) [NeZero n]

/-- The whole-world operator of one reversed-Hadamard pass: the program's gate
`ihGate n σ` lifted at the program's register `ihReg n σ`. -/
noncomputable def passOpIH (σ : ℕ × ℕ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  regLift ⟨ihReg n σ, (Reg.single (ictrl n σ)).inj⟩ (ihGate n σ)

/-- The whole-world operator of one inverted controlled-phase pass: the
program's gate `iladGate n σ` lifted at the program's register `iladReg n σ`;
`1` where the register expression degenerates, matching `iladGate`. -/
noncomputable def passOpILad (σ : ℕ × ℕ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  if h : ictrl n σ ≠ itgt n σ then
    regLift ⟨iladReg n σ, (Reg.pair _ _ h).inj⟩ (iladGate n σ)
  else 1

variable (x : Fin n → Bool)

/-- One reversed-Hadamard pass undoes the mid-stage family
(`qftStageMidN_step_H`). -/
theorem passOpIH_prodV {k' : ℕ} (hk : k' < n) :
    passOpIH n (k', 0) (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftStageMidN n x (n - 1 - k')))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (qftStageFam n x (n - 1 - k')) := by
  have hop : passOpIH n (k', 0)
      = regLift (Reg.single (cell n (n - 1 - k')))
          (singleGate (QubitD n) (cell n (n - 1 - k')) H) := rfl
  rw [hop, regLift_singleGate_prodV]
  exact congrArg _ (qftStageMidN_step_H n x (by omega))

/-- One inverted controlled-phase pass walks the ladder family one step
backwards (`cphase_vpair_phaseKet` at the inverted angle +
`qftLadderFamN_step_rev`). -/
theorem passOpILad_prodV {k' j' : ℕ} (hk : k' < n) (hj : j' < k') :
    passOpILad n (k', j') (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftLadderFamN n x (n - 1 - k') (k' - j')))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (qftLadderFamN n x (n - 1 - k') (k' - (j' + 1))) := by
  have hne : ictrl n (k', j') ≠ itgt n (k', j') := ictrl_ne_itgt n (by omega) (by omega)
  have hgate : iladGate n (k', j') = pairGate (D := QubitD n) (ictrl n (k', j'))
      (itgt n (k', j')) hne (cphase (-(2 * Real.pi / 2 ^ (k' - 1 - j' + 2)))) := by
    simp only [iladGate]
    rw [dif_pos hne]
  have hop : passOpILad n (k', j')
      = regLift (D := QubitD n) (Reg.pair (ictrl n (k', j')) (itgt n (k', j')) hne)
          (pairGate (D := QubitD n) (ictrl n (k', j')) (itgt n (k', j')) hne
            (cphase (-(2 * Real.pi / 2 ^ (k' - 1 - j' + 2))))) := by
    rw [passOpILad, dif_pos hne, hgate]
    rfl
  rw [hop]
  exact regLift_cphase_neg_qftLadderFamN n x hk hj hne

/-- The composite of the reversed ladder of the stage at counter `k'`. -/
noncomputable def iqftSubOp (k' : ℕ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  chainOp (List.finRange k') fun j' => passOpILad n (k', (j' : ℕ))

/-- The composite of one reversed stage: the inverted ladder, then the
Hadamard — the body of `iqftIter` in program order. -/
noncomputable def iqftStageOp (k' : ℕ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  passOpIH n (k', 0) ∘ₗ iqftSubOp n k'

/-- The composite of the reversed stage loop `iqftIter`. -/
noncomputable def iqftIterOp : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  chainOp (List.finRange n) fun k' => iqftStageOp n (k' : ℕ)

/-- **The composite operator of the verified circuit `iqftRevCir`**: every
gate the program applies, in the order the program applies them — the swap
block's composite is the QFT file's own `revCircOp`. -/
noncomputable def iqftRevCirOp : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  iqftIterOp n ∘ₗ revCircOp n

/-- The reversed-ladder composite walks the ladder family end to end,
backwards. -/
theorem iqftSubOp_prodV {k' : ℕ} (hk : k' < n) :
    iqftSubOp n k' (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftStageFam n x (n - k')))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (qftStageMidN n x (n - 1 - k')) := by
  have hfam : qftLadderFamN n x (n - 1 - k') (k' - 0) = qftStageFam n x (n - k') := by
    calc qftLadderFamN n x (n - 1 - k') (k' - 0)
        = qftLadderFamN n x (n - 1 - k') (n - 1 - (n - 1 - k')) := by
          rw [Nat.sub_zero]
          congr 1
          omega
      _ = qftStageFam n x ((n - 1 - k') + 1) := qftLadderFamN_full n x (by omega)
      _ = qftStageFam n x (n - k') := by
          congr 1
          omega
  have hexit : qftLadderFamN n x (n - 1 - k') (k' - k')
      = qftStageMidN n x (n - 1 - k') := by
    rw [Nat.sub_self]
    exact qftLadderFamN_zero n x (n - 1 - k')
  rw [show prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftStageFam n x (n - k'))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (qftLadderFamN n x (n - 1 - k') (k' - 0)) from congrArg _ hfam.symm,
    iqftSubOp, chainOp_finRange_family _
      (fun m => prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftLadderFamN n x (n - 1 - k') (k' - m)))
      (fun j' => passOpILad_prodV n x hk j'.isLt)]
  exact congrArg _ hexit

/-- One reversed-stage composite steps the stage family backwards. -/
theorem iqftStageOp_prodV {k' : ℕ} (hk : k' < n) :
    iqftStageOp n k' (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftStageFam n x (n - k')))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (qftStageFam n x (n - (k' + 1))) := by
  have hidx : n - (k' + 1) = n - 1 - k' := by omega
  rw [iqftStageOp, LinearMap.comp_apply, iqftSubOp_prodV n x hk, passOpIH_prodV n x hk,
    hidx]

/-- The reversed stage-loop composite takes the stage-complete profile back to
`∣x⟩`. -/
theorem iqftIterOp_prodV :
    iqftIterOp n (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftStageFam n x n))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftStageFam n x 0) := by
  have h := chainOp_finRange_family (fun k' : Fin n => iqftStageOp n (k' : ℕ))
    (fun m => prodV (QubitD n) (W := (univ : Finset (QubitL n)))
      (qftStageFam n x (n - m)))
    (fun k' => iqftStageOp_prodV n x k'.isLt)
  rw [Nat.sub_self] at h
  exact h

/-- **The circuit composite inverts the DFT on every Fourier profile**: the
operator assembled from the reversed circuit's gates sends `fourierState n x`
to `∣x⟩` — the operator form of `iqftRevDeriv`'s endpoints. -/
theorem iqftRevCirOp_fourierState :
    iqftRevCirOp n (fourierState n x)
      = deltav (QubitD n)
          (fun i : ↥(univ : Finset (QubitL n)) => x (i : QubitL n)) := by
  rw [iqftRevCirOp, LinearMap.comp_apply,
    show fourierState n x = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftRevFam (fun j : Fin n => phaseKet (qftAngle x (n - 1 - (j : ℕ)))) 0) from
      (fourierState_eq_prodV n x).trans (congrArg _ (qftRevFam_zero _).symm),
    revCircOp_prodV_fam n _,
    show prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftRevFam (fun j : Fin n => phaseKet (qftAngle x (n - 1 - (j : ℕ)))) (n / 2))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftStageFam n x n) from
      congrArg _ ((iqftRevFamN_half n x).trans (qftStageFam_full n x).symm),
    iqftIterOp_prodV n x,
    show qftStageFam n x 0 = fun i => qbit (x i) from qftStageFam_zero n x]
  exact prodV_qbit_eq_deltav n x

end

/-- **The operator-level IQFT theorem**: the ordered composite of the reversed
circuit's gates **is** the library operator `iqftOp n = (qftOp n)†`
(`Qhl/Register/Fourier.lean` §10) — the operator §1's one-gate form applies
and QPE consumes. Proof: post-composing with the unitary `qftOp n`, both sides
send every basis ket `∣x⟩` through `fourierState n x` to `∣x⟩`
(`qftOp_deltav`, `iqftRevCirOp_fourierState`, `iqftOp_fourierState`), so the
composites agree on the canonical basis (`linM_ext`); cancelling the unitary
gives the operators themselves. -/
theorem iqftRevCirOp_eq_iqftOp (n : ℕ) [NeZero n] :
    iqftRevCirOp n = (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n))) := by
  have hcomp : iqftRevCirOp n
        ∘ₗ (qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
            HS (QubitD n) (univ : Finset (QubitL n)))
      = (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
            HS (QubitD n) (univ : Finset (QubitL n)))
        ∘ₗ (qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
            HS (QubitD n) (univ : Finset (QubitL n))) :=
    linM_ext (QubitD n) fun m => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        qftOp_deltav n (fun i => m ⟨i, Finset.mem_univ i⟩),
        iqftRevCirOp_fourierState n (fun i => m ⟨i, Finset.mem_univ i⟩),
        iqftOp_fourierState n (fun i => m ⟨i, Finset.mem_univ i⟩)]
  refine LinearMap.ext fun v => ?_
  have hUadj : (qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n)))
      ((iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n))) v) = v := by
    have hcoe : (qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n)))
        = LinearMap.adjoint (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
            HS (QubitD n) (univ : Finset (QubitL n))) := by
      rw [coe_iqftOp, LinearMap.adjoint_adjoint]
    rw [hcoe]
    exact adjoint_apply_apply (iqftOp n).isUnitary v
  calc iqftRevCirOp n v
      = iqftRevCirOp n ((qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n)))
            ((iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
              HS (QubitD n) (univ : Finset (QubitL n))) v)) := by rw [hUadj]
    _ = (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n)))
        ((qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n)))
            ((iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
              HS (QubitD n) (univ : Finset (QubitL n))) v)) :=
        LinearMap.congr_fun hcomp _
    _ = (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) v := by rw [hUadj]

/-- **The readout action, certified by the verified circuit** — the fact the
phase-estimation readout consumes (`Qhl/Examples/QPETriple.lean`): the library
operator `iqftOp n` maps the product of phase kets to the product of basis
kets. Unlike the library's own `iqftOp_prodV_phaseKet`, this is derived from
the **verified reversed circuit**: the composite of the circuit's gates sends
the Fourier state to `∣x⟩` (`iqftRevCirOp_fourierState`), and the operator
identity `iqftRevCirOp_eq_iqftOp` transfers that action to `iqftOp n` — so a
consumer of this lemma formally depends on the gate-level circuit
verification of §2–§7, not merely on the operator's definition. -/
theorem iqftOp_prodV_phaseKet_of_circuit (n : ℕ) [NeZero n] (x : Fin n → Bool) :
    (iqftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n)))
        (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          fun j => phaseKet (qftAngle x (n - 1 - (j : ℕ))))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n))) fun j => qbit (x j) := by
  rw [← iqftRevCirOp_eq_iqftOp n, ← fourierState_eq_prodV n x,
    iqftRevCirOp_fourierState n x]
  exact (prodV_qbit_eq_deltav n x).symm

end Qhl.InverseQFTTriple

namespace Qhl.InverseQFTSource
open Finset QFTTriple InverseQFTTriple
variable (n : ℕ) [NeZero n] (x : Fin n → Bool)

/-- The backward reversal uses the fixed basis label in its invariant. -/
theorem revCircBack_deriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ)
          (iqftRevFamN n x 0))
        (fun σ : ℕ × ℕ => norm_prodV_eq_one _ (norm_iqftRevFamN n x 0))) fun _ => True)
      (revCirc n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ)
          (iqftRevFamN n x (n / 2)))
        (fun σ : ℕ × ℕ =>
          norm_prodV_eq_one _ (norm_iqftRevFamN n x (n / 2)))) fun _ => True) := by
  refine SourceDerivTot.countedStateChainVar (CounterLens.fst ℕ) (fun _ => n / 2) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (iqftRevFamN n x m))
    (fun m σ => norm_prodV_eq_one _ (norm_iqftRevFamN n x m))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · exact SourceDerivTot.countedRung_pair_fam (swapReg n) (swapGate n)
      (fun σ => QFTTriple.ctrl n σ) (fun σ => QFTTriple.mir n σ)
      (fun σ hσ => QFTTriple.ctrl_ne_mir n (σ := σ) hσ.2) (fun _ => SWAP)
      (fun σ => norm_iqftRevFamN n x σ.1)
      (fun σ => norm_iqftRevFamN n x (σ.1 + 1))
      (fun σ hσ => by
        have hne := QFTTriple.ctrl_ne_mir n (σ := σ) hσ.2
        refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
        change regLift (D := QubitD n)
          ⟨QFTTriple.swapReg n σ, (Reg.pair _ _ hne).inj⟩
          (QFTTriple.swapGate n σ) =
          regLift (D := QubitD n)
            (Reg.pair (QFTTriple.ctrl n σ) (QFTTriple.mir n σ) hne)
            (pairGate (D := QubitD n)
              (QFTTriple.ctrl n σ) (QFTTriple.mir n σ) hne SWAP)
        rw [show QFTTriple.swapGate n σ = pairGate (D := QubitD n)
            (QFTTriple.ctrl n σ) (QFTTriple.mir n σ) hne SWAP from by
          simp only [QFTTriple.swapGate]; rw [dif_pos hne]]
        rfl)
      (fun σ hσ => by
        have hk : σ.1 < n / 2 := hσ.2
        have hc : QFTTriple.ctrl n σ = cell n σ.1 := rfl
        have hm : QFTTriple.mir n σ = cell n (n - 1 - σ.1) := rfl
        exact ⟨phaseKet (qftAngle x σ.1),
          phaseKet (qftAngle x (n - 1 - σ.1)),
          by rw [hc, hm, iqftRevFamN_left n x hk, iqftRevFamN_right n x hk, SWAP_vpair],
          by rw [hc, hm]; exact iqftRevFamN_step n x hk⟩)
  · intro z
    exact SourceDerivTot.unitary_identity (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := σ) hσ.2.1)).inj

theorem iqftSub_current {φ : ℕ × ℕ → Prop}
    (hφ : ∀ σ v, φ ((CounterLens.snd ℕ).set σ v) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1 < n) :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : ℕ × ℕ =>
        prodV (QubitD n) (W := univ) (qftStageFam n x (n - σ.1)))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n x (n - σ.1)))) φ)
      (iqftSub n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : ℕ × ℕ =>
        prodV (QubitD n) (W := univ) (qftStageMidN n x (n - 1 - σ.1)))
        (fun σ => norm_prodV_eq_one _
          (norm_qftStageMidN n x (n - 1 - σ.1)))) φ) := by
    refine SourceDerivTot.countedStateChainVar (CounterLens.snd ℕ)
      (fun σ => σ.1) φ hφ (fun _ _ => rfl)
      (fun m σ => prodV (QubitD n) (W := univ)
        (qftLadderFamN n x (n - 1 - σ.1) (σ.1 - m)))
      (fun m σ => norm_prodV_eq_one _
        (norm_qftLadderFamN n x (n - 1 - σ.1) (σ.1 - m)))
      (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
    · intro σ hσ
      apply congrArg
      have hlt := hk σ hσ
      calc
        qftLadderFamN n x (n - 1 - σ.1) (σ.1 - 0) =
            qftLadderFamN n x (n - 1 - σ.1) (n - 1 - (n - 1 - σ.1)) := by
          congr 1
          omega
        _ = qftStageFam n x ((n - 1 - σ.1) + 1) :=
          qftLadderFamN_full n x (by omega)
        _ = qftStageFam n x (n - σ.1) := by congr 1; omega
    · intro σ _
      rw [Nat.sub_self]
      exact congrArg _ (qftLadderFamN_zero n x (n - 1 - σ.1))
    · exact SourceDerivTot.countedRung_fam (iladReg n) (iladGate n) _ _
        fun σ hσ => iladder_action n x σ (hk σ hσ.1) hσ.2
    · intro z
      exact SourceDerivTot.unitary_identity (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := σ) (hk σ hσ.1) hσ.2.1)).inj

/-- Reverse stages use the QFT stage family at the decreasing index. -/
theorem iqftIter_deriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ)
          (qftStageFam n x n))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n x n))) fun _ => True)
      (iqftIter n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ)
          (qftStageFam n x 0))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n x 0))) fun _ => True) := by
  refine SourceDerivTot.countedStateChainVar (CounterLens.fst ℕ) (fun _ => n) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (qftStageFam n x (n - m)))
    (fun m σ => norm_prodV_eq_one _ (norm_qftStageFam n x (n - m)))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => by rw [Nat.sub_self]) ?_ ?_
  · refine SourceDerivTot.seq (iqftSub_current n x
      (φ := fun σ => True ∧ σ.1 < n) (fun _ _ => Iff.rfl) (fun _ h => h.2)) ?_
    exact SourceDerivTot.countedRung_single_fam (ihReg n) (ihGate n)
      (fun σ => InverseQFTTriple.ictrl n σ) (fun _ => H)
      (fun σ => norm_qftStageMidN n x (n - 1 - σ.1))
      (fun σ => norm_qftStageFam n x (n - (σ.1 + 1)))
      (fun σ _ => ⟨(Reg.single (InverseQFTTriple.ictrl n σ)).inj, rfl⟩)
      (fun σ hσ => by
        change Function.update _ (cell n (n - 1 - σ.1)) _ = _
        rw [show n - (σ.1 + 1) = n - 1 - σ.1 from by omega]
        exact qftStageMidN_step_H n x (by have h := hσ.2; omega))
  · intro z
    refine SourceDerivTot.seq ?_
      (SourceDerivTot.unitary_identity (ihReg n) (ihGate n) _
        (fun σ _ => (Reg.single (InverseQFTTriple.ictrl n σ)).inj))
    refine SourceDerivTot.countedIdentity (CounterLens.snd ℕ) (fun σ => σ.1) _
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) _ ?_ ?_
    · exact SourceDerivTot.unitary_identity (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := σ) hσ.1.2.1 hσ.2)).inj
    · intro z'
      exact SourceDerivTot.unitary_identity (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := σ) hσ.1.2.1 hσ.2.1)).inj

theorem iqftRevDeriv : SourceDerivTot
    (SourceAssertion.ofAssn (QFTSource.outputAssn n x) (fun _ => True)) (iqftRevCir n)
    (SourceAssertion.ofAssn (QFTSource.inputAssn n x) (fun _ => True)) := by
  refine SourceDerivTot.seq (SourceDerivTot.conseq ?_ (revCircBack_deriv n x) ?_)
    (SourceDerivTot.conseq (SourceAssertion.entails_refl _) (iqftIter_deriv n x) ?_)
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [QFTSource.outputAssn, Assn.ofState_op, Assn.ofStateFam_op]
      rw [fourierState_eq_prodV n x, iqftRevFamN_zero]
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [Assn.ofStateFam_op, iqftRevFamN_half, qftStageFam_full]
      exact le_rfl
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [QFTSource.inputAssn, Assn.ofState_op, Assn.ofStateFam_op, qftStageFam_zero]
      exact le_rfl

theorem iqftRevValid :
    validTot (QFTSource.outputAssn n x) (iqftRevCir n) (QFTSource.inputAssn n x) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (iqftRevDeriv n x).sound
/-- Product-state form used when placing the verified inverse circuit in QPE. -/
theorem iqftProdDeriv : SourceDerivTot
    (SourceAssertion.ofAssn
      (Assn.ofStateFam (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ)
        (fun i => phaseKet (qftAngle x (n - 1 - (i : ℕ)))))
        (fun _ => norm_prodV_eq_one _ fun _ => norm_phaseKet _)) (fun _ => True))
    (iqftRevCir n)
    (SourceAssertion.ofAssn
      (Assn.ofStateFam (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ)
        (fun i => qbit (x i)))
        (fun _ => norm_prodV_eq_one _ fun _ => norm_qbit _)) (fun _ => True)) := by
  refine SourceDerivTot.conseq ?_ (iqftRevDeriv n x) (SourceAssertion.entails_refl _)
  apply SourceAssertion.entails_ofAssn
  · intro _ h; exact h
  · intro σ _
    simp only [QFTSource.outputAssn, Assn.ofState_op, Assn.ofStateFam_op]
    rw [fourierState_eq_prodV n x]

end Qhl.InverseQFTSource
