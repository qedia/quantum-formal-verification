import Qhl.Logic.Source.CountedStateChain
import Qhl.Logic.Source.ProductStateFam
import Qhl.Logic.CountedProdChain
import Qhl.Logic.ProductStateFam
import Qhl.Logic.Soundness
import Qhl.Logic.WpChain
import Qhl.Register.Fourier

/-! # The quantum Fourier transform triple

CoqQ's QFT case study (`src/example/coqq_paper/example.v:154-345`) in `QHL⁺_tot`:
for every width `n ≥ 1` and **every** computational-basis input `x`,

```
⊨ₜ { ∣x⟩ }  qftCir n  { fourierState n x }.
```

**Every loop is a genuine `while` loop** — the printed proof system has no
`for` rule, so each loop is the counted shape
`cnt := 0 ; while cnt < N do BODY ; cnt := cnt + 1 od` (`countedProg`,
`Qhl/Logic/CountedWhile.lean`), discharged through the packaged product-state
rules of `Qhl/Logic/CountedProdChain.lean` — derived from the printed
constructors only: (Ax-Ass), (R-Seq), (R-Conseq), and **(R-Loop-tot)** with the
integer variant `t σ = N − cnt σ` — DEFINITE termination. The store is
`σT = ℕ × ℕ`: `σ.1` the stage counter (reused by the reversal loop), `σ.2` the
rung counter of the controlled-phase ladder.

| here | CoqQ (`example.v`) |
|---|---|
| `qftSub` / `qftSub_deriv` | `QFT_sub` (`:162`) / `RS_QFT_sub` |
| `qftIter` / `qftIter_deriv` | `QFT_iter` (`:167`) / `RS_QFT_iter` |
| `revCirc` / `revCirc_deriv` | `rev_circuit` (`:140`) / `RS_rev_circuit` |
| `qftCir` / `qftDeriv` | `QFT_cir` (`:173`) / `RS_QFT_cir` |

**How each loop is closed.** The stage and reversal loops use
`DerivTot.countedProdChainSource`. Their invariant-preservation derivations
read the family at the current counter without a fixed-rank mask. Separate
identity-predicate derivations preserve the classical counter and frame for
all quantum inputs. The ladder uses `countedStateChainVarSource`, reading both
its bound `n − 1 − σ.1` and its invariant family at the current stage. Its
integer rank is the natural subtraction cast to `Int`; the source constructor
also receives its nonnegativity proof. Gate actions remain the mathematical
premises `regLift_cphase_qftLadderFamN`, `qftStageMidN_eq_update_H`, and the
swap-family laws.

The registers are genuine store-dependent register expressions (`RegExpr`, the
paper's `q̄(t̄)`), reading the touched cell `cell n k` off the counter
(`Qhl/Register/Qubits.lean`). Off the loop masks a pair expression may
degenerate; there the bundled gate is `1` — those stores are unreachable under
the masks, and the paper's `Dist(q̄)` side condition (`unitaryPre`) is
discharged only where the masks hold.

The triple is non-vacuous in both directions: the precondition is literally the
computational basis state `∣x⟩` (`prodV_qbit_eq_deltav`) and the postcondition
the genuine DFT profile `fourierState n x` (`norm_fourierState`), reached
through its product form `fourierState_eq_prodV` (CoqQ `QFTbv_rev`, `:299`).
Both endpoints are store-constant, so the triple holds at an arbitrary initial
store; soundness is wired through by `qftValid`. `[NeZero n]` is forced by
totality of the register expressions; the `n = 0` circuit is empty.
-/

namespace Qhl.QFTTriple

open Finset

section

variable (n : ℕ) [NeZero n]

/-! ## §1. The registers and gates, as store-dependent expressions

The store is `σT = ℕ × ℕ`: `σ.1` is the stage counter, `σ.2` the rung
counter. -/

/-- The control cell of the current stage: cell `σ.1`. -/
def ctrl (σ : ℕ × ℕ) : QubitL n := cell n σ.1

/-- The target cell of the current ladder rung: cell `σ.1 + 1 + σ.2`, CoqQ's
`s.[i + j.+1]` (`example.v:164`), matching the library `finTarget`. -/
def tgt (σ : ℕ × ℕ) : QubitL n := cell n (σ.1 + 1 + σ.2)

/-- The mirror cell of the current reversal transposition: cell `n − 1 − σ.1`
(CoqQ `rev_ord`). -/
def mir (σ : ℕ × ℕ) : QubitL n := cell n (n - 1 - σ.1)

/-- The one-cell register expression `s.[i]` of the Hadamard step. -/
def hReg : RegExpr (ℕ × ℕ) (QubitL n) 1 := fun σ => (Reg.single (ctrl n σ)).toFun

/-- The Hadamard on the tuple space of the one-cell register. -/
noncomputable def hGate (σ : ℕ × ℕ) : UnitaryOp (TSpace (QubitD n) (hReg n σ)) :=
  singleGate (QubitD n) (ctrl n σ) H

/-- The two-cell register expression `(s.[i], s.[i + j.+1])` of a ladder
rung. -/
def ladReg : RegExpr (ℕ × ℕ) (QubitL n) 2 := fun σ => ![ctrl n σ, tgt n σ]

/-- The controlled phase `cphase (2π/2^(j+2))` of rung `j = σ.2`, on the tuple
space of the rung's register; `1` where the register expression degenerates
(off the loop masks only). -/
noncomputable def ladGate (σ : ℕ × ℕ) : UnitaryOp (TSpace (QubitD n) (ladReg n σ)) :=
  if h : ctrl n σ ≠ tgt n σ then
    pairGate (ctrl n σ) (tgt n σ) h (cphase (2 * Real.pi / 2 ^ (σ.2 + 2)))
  else 1

/-- The two-cell register expression `(s.[k], s.[n−1−k])` of a reversal
transposition. -/
def swapReg : RegExpr (ℕ × ℕ) (QubitL n) 2 := fun σ => ![ctrl n σ, mir n σ]

/-- The swap on the tuple space of the transposition's register; `1` where the
register expression degenerates (off the loop mask only). -/
noncomputable def swapGate (σ : ℕ × ℕ) : UnitaryOp (TSpace (QubitD n) (swapReg n σ)) :=
  if h : ctrl n σ ≠ mir n σ then pairGate (ctrl n σ) (mir n σ) h SWAP else 1

/-! ## §2. The programs (CoqQ `QFT_sub`, `QFT_iter`, `rev_circuit`, `QFT_cir`)

Each loop is the counted `while` shape (`countedProg`): program constructors
`.assign`, `.while`, `.seq`, `.unitary` only. -/

/-- **CoqQ `QFT_sub`** (`example.v:162`): the controlled-phase ladder of one QFT
stage, on the rung counter `σ.2`. The bound `n − 1 − σ.1` is read from the
store: the ladder length of the *current* stage. All rungs share the control
wire `s.[σ.1]`. -/
noncomputable def qftSub : Prog (ℕ × ℕ) (QubitD n) :=
  countedProg (.snd ℕ) (fun σ => n - 1 - σ.1)
    (.unitary 2 (ladReg n) (ladGate n))

/-- **CoqQ `QFT_iter`** (`example.v:167`): the stage loop, as a `while` loop on
the stage counter `σ.1`; each pass is one Hadamard on wire `σ.1` followed by
the ladder `qftSub`. -/
noncomputable def qftIter : Prog (ℕ × ℕ) (QubitD n) :=
  countedProg (.fst ℕ) (fun _ => n)
    ((Prog.unitary 1 (hReg n) (hGate n)).seq (qftSub n))

/-- **CoqQ `rev_circuit`** (`example.v:140`, `RevTuple`): the `⌊n/2⌋` swaps that
reverse the wire order, as a `while` loop on the (re-initialised) stage
counter. -/
noncomputable def revCirc : Prog (ℕ × ℕ) (QubitD n) :=
  countedProg (.fst ℕ) (fun _ => n / 2)
    (.unitary 2 (swapReg n) (swapGate n))

/-- **CoqQ `QFT_cir`** (`example.v:173`): `QFT_iter ;; rev_circuit`. -/
noncomputable def qftCir : Prog (ℕ × ℕ) (QubitD n) := (qftIter n).seq (revCirc n)

/-! ## §3. The loop invariants, as store-constant assertions

The library families `qftStageFam` (§8), `qftStageMidN`/`qftLadderFamN`/
`qftRevFamN` (§9b), each wrapped into the projector assertion
`Assn.ofState (prodV …)`; counter insensitivity is definitional. -/

variable (x : Fin n → Bool)

/-- Stage invariant, as a store-constant assertion. -/
noncomputable def stageAssn (k : ℕ) : Assn (ℕ × ℕ) (QubitD n) :=
  Assn.ofState (prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftStageFam n x k))
    (norm_prodV_eq_one _ (norm_qftStageFam n x k))

/-- Mid-stage invariant, as a store-constant assertion. -/
noncomputable def midAssn (k : ℕ) : Assn (ℕ × ℕ) (QubitD n) :=
  Assn.ofState (prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftStageMidN n x k))
    (norm_prodV_eq_one _ (norm_qftStageMidN n x k))

/-- Reversal invariant, as a store-constant assertion family. -/
noncomputable def revAssn (m : ℕ) : Assn (ℕ × ℕ) (QubitD n) :=
  Assn.ofState (prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftRevFamN n x m))
    (norm_prodV_eq_one _ (norm_qftRevFamN n x m))

/-! ## §4. The mask arithmetic: the touched cells are distinct -/

theorem ctrl_ne_tgt {σ : ℕ × ℕ} (hk : σ.1 < n) (hj : σ.2 < n - 1 - σ.1) :
    ctrl n σ ≠ tgt n σ :=
  cell_ne n hk (by omega) (by omega)

theorem ctrl_ne_mir {σ : ℕ × ℕ} (hk : σ.1 < n / 2) : ctrl n σ ≠ mir n σ :=
  cell_ne n (by omega) (by omega) (by omega)

/-! ## §5. The subroutine triple (CoqQ `RS_QFT_sub`) -/

/-- The controlled-phase gate advances the ladder family at the current store. -/
private theorem ladder_action (σ : ℕ × ℕ) (hk : σ.1 < n)
    (hj : σ.2 < n - 1 - σ.1) :
    ∃ hinj : Function.Injective (ladReg n σ),
      regLift ⟨ladReg n σ, hinj⟩ (ladGate n σ)
        (prodV (QubitD n) (W := univ) (qftLadderFamN n x σ.1 σ.2)) =
        prodV (QubitD n) (W := univ) (qftLadderFamN n x σ.1 (σ.2 + 1)) := by
  have hne : ctrl n σ ≠ tgt n σ := ctrl_ne_tgt n hk hj
  refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
  rw [show regLift ⟨ladReg n σ, (Reg.pair _ _ hne).inj⟩ (ladGate n σ)
      = regLift (D := QubitD n) (Reg.pair (ctrl n σ) (tgt n σ) hne)
          (pairGate (D := QubitD n) (ctrl n σ) (tgt n σ) hne
            (cphase (2 * Real.pi / 2 ^ (σ.2 + 2)))) from by
    rw [show ladGate n σ = pairGate (ctrl n σ) (tgt n σ) hne
        (cphase (2 * Real.pi / 2 ^ (σ.2 + 2))) from by
      simp only [ladGate]; rw [dif_pos hne]]
    rfl]
  exact regLift_cphase_qftLadderFamN n x hk hj hne

/-- The ladder at the current stage, with any classical frame insensitive to its counter. -/
theorem qftSub_current {φ : (ℕ × ℕ) → Prop}
    (hφ : ∀ σ v, φ (σ.1, v) ↔ φ σ) (hk : ∀ σ, φ σ → σ.1 < n) :
    DerivTot ((Assn.ofFam Prod.fst
      (fun m => prodA (QubitD n) (qftStageMidN n x m) (norm_qftStageMidN n x m))).mask φ) (qftSub n)
      ((Assn.ofFam (fun σ => σ.1 + 1)
        (fun m => prodA (QubitD n) (qftStageFam n x m) (norm_qftStageFam n x m))).mask φ) := by
  have h : DerivTot
      ((Assn.ofStateFam (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ) (qftStageMidN n x σ.1))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageMidN n x σ.1))).mask φ) (qftSub n)
      ((Assn.ofStateFam (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ) (qftStageFam n x (σ.1 + 1)))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n x (σ.1 + 1)))).mask φ) := by
    refine DerivTot.countedStateChainVarSource (CounterLens.snd ℕ) hφ (fun _ _ => rfl)
      (fun m σ => prodV (QubitD n) (W := univ) (qftLadderFamN n x σ.1 m))
      (fun m σ => norm_prodV_eq_one _ (norm_qftLadderFamN n x σ.1 m))
      (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
    · intro σ _
      exact congrArg _ (qftLadderFamN_zero n x σ.1)
    · intro σ hσ
      exact congrArg _ (qftLadderFamN_full n x (hk σ hσ))
    · exact DerivTot.countedRung_fam (ladReg n) (ladGate n) _ _
        fun σ hσ => ladder_action n x σ (hk σ hσ.1) hσ.2
    · intro z
      exact DerivTot.unitary_identityMask (ladReg n) (ladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (ctrl_ne_tgt n (hk σ hσ.1) hσ.2.1)).inj
  exact DerivTot.conseq
    (Assn.mask_le_mask (fun _ hσ => hσ) (fun σ _ => le_of_eq (by
      rw [Assn.ofFam_op, prodA_op, Assn.ofStateFam_op]))) h
    (Assn.mask_le_mask (fun _ hσ => hσ) (fun σ _ => le_of_eq (by
      rw [Assn.ofFam_op, prodA_op, Assn.ofStateFam_op])))

/-- The fixed-stage ladder triple, obtained from the current-stage source derivation. -/
theorem qftSub_deriv (k : ℕ) :
    DerivTot ((midAssn n x k).mask fun σ => σ.1 = k ∧ k < n) (qftSub n)
      ((stageAssn n x (k + 1)).mask fun σ => σ.1 = k ∧ k < n) := by
  refine DerivTot.conseq
    (Assn.mask_le_mask (fun _ h => h) (fun σ hσ => le_of_eq ?_))
    (qftSub_current n x (fun _ _ => Iff.rfl) (fun σ hσ => by omega))
    (Assn.mask_le_mask (fun _ h => h) (fun σ hσ => le_of_eq ?_))
  · rw [Assn.ofFam_op, hσ.1, prodA_op, midAssn, Assn.ofState_op]
  · rw [Assn.ofFam_op, hσ.1, prodA_op, stageAssn, Assn.ofState_op]

/-! ## §6. The iteration triple (CoqQ `RS_QFT_iter`) -/

/-- **CoqQ `RS_QFT_iter`**: the stage loop takes the computational basis state
`∣x⟩` to the product of phase kets — the Fourier state up to the wire reversal.
One `DerivTot.countedProdChainSource` on the stage counter along `qftStageFam`
uses the Hadamard action followed by `qftSub_current` for preservation.
An independent identity derivation establishes decrease on all quantum inputs. -/
theorem qftIter_deriv :
    DerivTot (stageAssn n x 0) (qftIter n)
      ((stageAssn n x n).mask fun σ => σ.1 = n) := by
  refine DerivTot.countedProdChainSource (CounterLens.fst ℕ)
    (hψ₀ := norm_qftStageFam n x 0) (hψ₁ := norm_qftStageFam n x n)
    (qftStageFam n x) (norm_qftStageFam n x) rfl rfl ?_ ?_
  · have hs := qftSub_current n x (φ := fun σ => σ.1 < n)
      (fun _ _ => Iff.rfl) (fun _ h => h)
    rw [Assn.ofFam_prodA, Assn.ofFam_prodA] at hs
    rw [Assn.ofFam_prodA, Assn.ofFam_prodA]
    refine DerivTot.seq ?_ hs
    exact DerivTot.countedRung_single_fam (hReg n) (hGate n) (ctrl n) (fun _ => H)
      (fun σ => norm_qftStageFam n x σ.1) (fun σ => norm_qftStageMidN n x σ.1)
      (fun σ _ => ⟨(Reg.single (ctrl n σ)).inj, rfl⟩)
      (fun σ hσ => qftStageMidN_eq_update_H n x hσ)
  · intro k
    refine DerivTot.seq
      (DerivTot.unitary_identityMask (hReg n) (hGate n) _
        (fun σ _ => (Reg.single (ctrl n σ)).inj)) ?_
    exact DerivTot.countedIdentityVarSource (CounterLens.snd ℕ)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
      (DerivTot.unitary_identityMask (ladReg n) (ladGate n) _
        (fun σ hσ => (Reg.pair _ _ (ctrl_ne_tgt n (by
          have h := hσ.1; change σ.1 = k ∧ k < n at h; omega) hσ.2)).inj))
      (fun z => DerivTot.unitary_identityMask (ladReg n) (ladGate n) _
        (fun σ hσ => (Reg.pair _ _ (ctrl_ne_tgt n (by
          have h := hσ.1; change σ.1 = k ∧ k < n at h; omega) hσ.2.1)).inj))

/-! ## §7. The reversal triple (CoqQ `RS_rev_circuit`) -/

/-- **CoqQ `RS_rev_circuit`** (`example.v:133`): the swap network reverses the
wire order. One `DerivTot.countedProdChainSource` with bound `⌊n/2⌋` along
`qftRevFamN`; each swap uses `countedRung_pair_fam` over `SWAP_vpair`,
with a separate identity-predicate gate derivation. -/
theorem revCirc_deriv :
    DerivTot (revAssn n x 0) (revCirc n)
      ((revAssn n x (n / 2)).mask fun σ => σ.1 = n / 2) := by
  refine DerivTot.countedProdChainSource (CounterLens.fst ℕ)
    (hψ₀ := norm_qftRevFamN n x 0) (hψ₁ := norm_qftRevFamN n x (n / 2))
    (qftRevFamN n x) (norm_qftRevFamN n x) rfl rfl ?_ ?_
  · rw [Assn.ofFam_prodA, Assn.ofFam_prodA]
    exact DerivTot.countedRung_pair_fam (swapReg n) (swapGate n) (ctrl n) (mir n)
      (fun σ hσ => ctrl_ne_mir n hσ)
      (fun _ => SWAP)
      (fun σ => norm_qftRevFamN n x σ.1) (fun σ => norm_qftRevFamN n x (σ.1 + 1))
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
        exact ⟨phaseKet (qftAngle x (n - 1 - σ.1)), phaseKet (qftAngle x σ.1),
          by rw [hc, hm, qftRevFamN_left n x hk, qftRevFamN_right n x hk, SWAP_vpair],
          by rw [hc, hm]; exact qftRevFamN_step n x hk⟩)
  · intro k
    exact DerivTot.unitary_identityMask (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (ctrl_ne_mir n (by
        change σ.1 = k ∧ k < n / 2 at hσ; omega))).inj

/-! ## §8. The QFT triple (CoqQ `RS_QFT_cir`) -/

/-- **The QFT derivation** — CoqQ `RS_QFT_cir`. For every width `n ≥ 1` and
every computational-basis input `x`,

```
⊢ₜ { ∣x⟩ }  qftCir n  { fourierState n x }
```

over the store `σT = ℕ × ℕ` at an arbitrary initial store: (R-Seq) of
`qftIter_deriv` and `revCirc_deriv`, with (R-Conseq) collapsing the counter
masks at the endpoints — the endpoints themselves are store-constant. The
postcondition is turned into the genuine DFT state by the library's
`fourierState_eq_prodV` (CoqQ `QFTbv_rev`, `:299`). -/
theorem qftDeriv :
    DerivTot (σT := ℕ × ℕ)
      (Assn.ofState (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (fun i => qbit (x i))) (norm_prodV_eq_one _ fun _ => norm_qbit _))
      (qftCir n)
      (Assn.ofState (fourierState n x) (norm_fourierState n x)) :=
  DerivTot.seq
    (DerivTot.conseq
      (Assn.ofState_le_ofState
        (congrArg _ (qftStageFam_zero n x).symm))
      (qftIter_deriv n x)
      (Assn.mask_le_of_imp_le fun σ _ => le_of_eq (by
        simp only [stageAssn, revAssn, Assn.ofState_op, qftRevFamN, qftRevFam_zero,
          qftStageFam_full])))
    (DerivTot.conseq (Assn.le_refl' _) (revCirc_deriv n x)
      (Assn.mask_le_of_imp_le fun σ _ => le_of_eq (by
        simp only [revAssn, Assn.ofState_op, qftRevFamN, qftRevFam_half]
        rw [fourierState_eq_prodV n x]
        simp only [revIdx_val])))

/-- **The QFT triple, semantically** — `qftDeriv` through soundness. -/
theorem qftValid :
    validTot (σT := ℕ × ℕ)
      (Assn.ofState (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (fun i => qbit (x i))) (norm_prodV_eq_one _ fun _ => norm_qbit _))
      (qftCir n)
      (Assn.ofState (fourierState n x) (norm_fourierState n x)) :=
  (qftDeriv n x).sound

end

/-- **Non-vacuity of the precondition**: it is literally the computational basis
state `∣x⟩` (CoqQ `t2tv_tuple`). Together with `norm_fourierState` — the
postcondition is a unit vector, hence not the zero assertion — the triple is
genuine in both directions. -/
theorem prodV_qbit_eq_deltav (n : ℕ) (x : Fin n → Bool) :
    prodV (QubitD n) (W := (univ : Finset (QubitL n))) (fun i => qbit (x i))
      = deltav (QubitD n) (fun i : ↥(univ : Finset (QubitL n)) => x (i : QubitL n)) :=
  prodV_single (QubitD n) (fun i => x i)

/-! ## §9. The composite operator of the verified circuit

`qftDeriv` states the circuit's action **per basis input**: one triple for each
`x`. Since the basis action for *every* `x` determines a linear operator, the
verified circuit also carries an **operator-level** statement: the ordered
composite of the very gates the program applies equals the library's Fourier
operator `qftOp n` (`Qhl/Register/Fourier.lean` §10) — which was defined
*independently of any circuit*, from the orthonormality of the Fourier profiles
(`inner_fourierState`, CoqQ `QFTbv_onb`), before this file existed.

* `passOpH`/`passOpLad`/`passOpSwap` — the whole-world operator of **one pass
  of the program**: the cylindrical extension (`regLift`) of the program's own
  gate expression (`hGate`/`ladGate`/`swapGate`) at the program's own register
  expression (`hReg`/`ladReg`/`swapReg`), read at the store the counted loop
  passes through. Off the loop masks a pair register may degenerate; there the
  operator is `1`, exactly as the program's gate is (`ladGate`/`swapGate`).
* `qftSubOp`/`qftStageOp`/`qftIterOp`/`revCircOp`/`qftCirOp` — the ordered
  composites of those passes (`chainOp`, `Qhl/Logic/WpChain.lean` §2), in the
  program's own order: `H`, then the ladder, stage by stage, then the swaps.
* the action lemmas are discharged by the **same family step laws the
  derivation uses** (`qftStageMidN_eq_update_H`, `qftLadderFamN_step`,
  `qftRevFam_step_cell` — §8–§9b of `Qhl/Register/Fourier.lean`).

The statement `qftCirOp n = qftOp n` (and its pointwise corollary at an
arbitrary, possibly superposed `ψ`) is a statement **about the operator
assembled from the verified circuit's gates**, proved by basis agreement
(`linM_ext`); it is a corollary *about* the verified object, not a triple of
the proof system — the program-logic content remains the per-basis triples
`qftDeriv`/`qftValid`. -/

section

variable (n : ℕ) [NeZero n]

/-- The whole-world operator of one Hadamard pass: the program's gate
`hGate n σ` lifted at the program's register `hReg n σ`. -/
noncomputable def passOpH (σ : ℕ × ℕ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  regLift ⟨hReg n σ, (Reg.single (ctrl n σ)).inj⟩ (hGate n σ)

/-- The whole-world operator of one controlled-phase pass: the program's gate
`ladGate n σ` lifted at the program's register `ladReg n σ`; `1` where the
register expression degenerates (off the loop masks only), matching
`ladGate`. -/
noncomputable def passOpLad (σ : ℕ × ℕ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  if h : ctrl n σ ≠ tgt n σ then
    regLift ⟨ladReg n σ, (Reg.pair _ _ h).inj⟩ (ladGate n σ)
  else 1

/-- The whole-world operator of one reversal-swap pass: the program's gate
`swapGate n σ` lifted at the program's register `swapReg n σ`; `1` where the
register expression degenerates (off the loop mask only), matching
`swapGate`. -/
noncomputable def passOpSwap (σ : ℕ × ℕ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  if h : ctrl n σ ≠ mir n σ then
    regLift ⟨swapReg n σ, (Reg.pair _ _ h).inj⟩ (swapGate n σ)
  else 1

variable (x : Fin n → Bool)

/-- One Hadamard pass acts on the stage family exactly as the derivation's
Hadamard rung says (`qftStageMidN_eq_update_H`). -/
theorem passOpH_prodV {k : ℕ} (hk : k < n) :
    passOpH n (k, 0) (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftStageFam n x k))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftStageMidN n x k) := by
  have hop : passOpH n (k, 0)
      = regLift (Reg.single (cell n k)) (singleGate (QubitD n) (cell n k) H) := rfl
  rw [hop, regLift_singleGate_prodV]
  exact congrArg _ (qftStageMidN_eq_update_H n x hk)

/-- One controlled-phase pass acts on the ladder family exactly as the
derivation's rung says (`cphase_vpair_phaseKet` + `qftLadderFamN_step`). -/
theorem passOpLad_prodV {k j : ℕ} (hk : k < n) (hj : j < n - 1 - k) :
    passOpLad n (k, j) (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftLadderFamN n x k j))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (qftLadderFamN n x k (j + 1)) := by
  have hne : ctrl n (k, j) ≠ tgt n (k, j) := ctrl_ne_tgt n hk hj
  have hgate : ladGate n (k, j) = pairGate (ctrl n (k, j)) (tgt n (k, j)) hne
      (cphase (2 * Real.pi / 2 ^ (j + 2))) := by
    simp only [ladGate]
    rw [dif_pos hne]
  have hop : passOpLad n (k, j)
      = regLift (D := QubitD n) (Reg.pair (ctrl n (k, j)) (tgt n (k, j)) hne)
          (pairGate (D := QubitD n) (ctrl n (k, j)) (tgt n (k, j)) hne
            (cphase (2 * Real.pi / 2 ^ (j + 2)))) := by
    rw [passOpLad, dif_pos hne, hgate]
    rfl
  rw [hop]
  exact regLift_cphase_qftLadderFamN n x hk hj hne

/-- One swap pass advances the reversal invariant — generically in the per-wire
family, so it serves the forward run here and the backward run of the
inverse-QFT circuit (`SWAP_vpair` + `qftRevFam_step_cell`). -/
theorem passOpSwap_prodV_fam (φv : Fin n → 𝕢) {k : ℕ} (hk : k < n / 2) :
    passOpSwap n (k, 0) (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftRevFam φv k))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftRevFam φv (k + 1)) := by
  have hne : ctrl n (k, 0) ≠ mir n (k, 0) := ctrl_ne_mir n hk
  have hgate : swapGate n (k, 0) = pairGate (ctrl n (k, 0)) (mir n (k, 0)) hne SWAP := by
    simp only [swapGate]
    rw [dif_pos hne]
  have hop : passOpSwap n (k, 0)
      = regLift (D := QubitD n) (Reg.pair (ctrl n (k, 0)) (mir n (k, 0)) hne)
          (pairGate (D := QubitD n) (ctrl n (k, 0)) (mir n (k, 0)) hne SWAP) := by
    rw [passOpSwap, dif_pos hne, hgate]
    rfl
  have hG : (SWAP :
        EuclideanSpace ℂ (QubitD n (ctrl n (k, 0)) × QubitD n (mir n (k, 0))) →ₗ[ℂ]
          EuclideanSpace ℂ (QubitD n (ctrl n (k, 0)) × QubitD n (mir n (k, 0))))
        (vpair (qftRevFam φv k (ctrl n (k, 0))) (qftRevFam φv k (mir n (k, 0))))
      = vpair (φv (cell n (n - 1 - k))) (φv (cell n k)) := by
    rw [show ctrl n (k, 0) = cell n k from rfl,
      show mir n (k, 0) = cell n (n - 1 - k) from rfl,
      qftRevFam_left_cell n φv hk, qftRevFam_right_cell n φv hk, SWAP_vpair]
  rw [hop, regLift_pairGate_prodV (ctrl n (k, 0)) (mir n (k, 0)) hne SWAP
    (qftRevFam φv k) hG]
  exact congrArg _ (qftRevFam_step_cell n φv hk)

/-- The composite of one stage's ladder — the passes of `qftSub` in program
order. -/
noncomputable def qftSubOp (k : ℕ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  chainOp (List.finRange (n - 1 - k)) fun j => passOpLad n (k, (j : ℕ))

/-- The composite of one whole stage: the Hadamard pass, then the ladder — the
body of `qftIter` in program order. -/
noncomputable def qftStageOp (k : ℕ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  qftSubOp n k ∘ₗ passOpH n (k, 0)

/-- The composite of the stage loop `qftIter`. -/
noncomputable def qftIterOp : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  chainOp (List.finRange n) fun k => qftStageOp n (k : ℕ)

/-- The composite of the reversal network `revCirc`. -/
noncomputable def revCircOp : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  chainOp (List.finRange (n / 2)) fun k => passOpSwap n ((k : ℕ), 0)

/-- **The composite operator of the verified circuit `qftCir`**: every gate the
program applies, in the order the program applies them. -/
noncomputable def qftCirOp : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  revCircOp n ∘ₗ qftIterOp n

/-- The ladder composite walks the ladder family end to end
(`chainOp_finRange_family` along `qftLadderFamN`). -/
theorem qftSubOp_prodV {k : ℕ} (hk : k < n) :
    qftSubOp n k (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftStageMidN n x k))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (qftStageFam n x (k + 1)) := by
  have h0 : prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftStageMidN n x k)
      = prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftLadderFamN n x k 0) :=
    congrArg _ (qftLadderFamN_zero n x k).symm
  rw [h0, qftSubOp, chainOp_finRange_family _
    (fun m => prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftLadderFamN n x k m))
    (fun j => passOpLad_prodV n x hk j.isLt)]
  exact congrArg _ (qftLadderFamN_full n x hk)

/-- One stage composite advances the stage family. -/
theorem qftStageOp_prodV {k : ℕ} (hk : k < n) :
    qftStageOp n k (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftStageFam n x k))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (qftStageFam n x (k + 1)) := by
  rw [qftStageOp, LinearMap.comp_apply, passOpH_prodV n x hk, qftSubOp_prodV n x hk]

/-- The stage-loop composite takes `∣x⟩` to the un-reversed phase profile. -/
theorem qftIterOp_prodV :
    qftIterOp n (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (qftStageFam n x 0))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftStageFam n x n) :=
  chainOp_finRange_family _
    (fun m => prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftStageFam n x m))
    (fun k => qftStageOp_prodV n x k.isLt)

/-- The reversal composite walks the reversal family end to end — generically
in the per-wire family. -/
theorem revCircOp_prodV_fam (φv : Fin n → 𝕢) :
    revCircOp n (prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftRevFam φv 0))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftRevFam φv (n / 2)) :=
  chainOp_finRange_family _
    (fun m => prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftRevFam φv m))
    (fun k => passOpSwap_prodV_fam n φv k.isLt)

/-- **The circuit composite realises the DFT on every basis input**: the
operator assembled from the program's gates sends `∣x⟩` to the Fourier profile
of `x` — the operator form of `qftDeriv`'s endpoints. -/
theorem qftCirOp_prodV_qbit :
    qftCirOp n (prodV (QubitD n) (W := (univ : Finset (QubitL n)))
        (fun i => qbit (x i)))
      = fourierState n x := by
  rw [qftCirOp, LinearMap.comp_apply,
    show prodV (QubitD n) (W := (univ : Finset (QubitL n))) (fun i => qbit (x i))
      = prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftStageFam n x 0) from
      congrArg _ (qftStageFam_zero n x).symm,
    qftIterOp_prodV n x,
    show prodV (QubitD n) (W := (univ : Finset (QubitL n))) (qftStageFam n x n)
      = prodV (QubitD n) (W := (univ : Finset (QubitL n)))
          (qftRevFam (fun i => phaseKet (qftAngle x (i : ℕ))) 0) from
      congrArg _ ((qftStageFam_full n x).trans (qftRevFam_zero _).symm),
    revCircOp_prodV_fam n _, fourierState_eq_prodV n x]
  exact congrArg _ (qftRevFam_half _)

/-- The circuit composite on a computational basis ket. -/
theorem qftCirOp_deltav :
    qftCirOp n (deltav (QubitD n)
        (fun i : ↥(univ : Finset (QubitL n)) => x (i : QubitL n)))
      = fourierState n x := by
  rw [← prodV_qbit_eq_deltav n x]
  exact qftCirOp_prodV_qbit n x

end

/-- **The operator-level QFT theorem** — the audit's `U_QFT = F_n`: the ordered
composite of the verified circuit's gates **is** the Fourier operator `qftOp n`
of `Qhl/Register/Fourier.lean` §10 — an operator defined independently of any
circuit, from the orthonormality of the Fourier profiles (`inner_fourierState`,
CoqQ `QFTbv_onb`). Proof: both operators agree on every computational basis ket
(`qftCirOp_deltav` vs `qftOp_deltav`), and linear maps agreeing on the
canonical basis are equal (`linM_ext`, CoqQ `lfunPD`). -/
theorem qftCirOp_eq_qftOp (n : ℕ) [NeZero n] :
    qftCirOp n = (qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
        HS (QubitD n) (univ : Finset (QubitL n))) :=
  linM_ext (QubitD n) fun k => by
    rw [qftCirOp_deltav n (fun i => k ⟨i, Finset.mem_univ i⟩),
      qftOp_deltav n (fun i => k ⟨i, Finset.mem_univ i⟩)]

/-- **The basis-independent corollary**: on **every** input `ψ` — superposed or
not — the circuit's composite acts as the Fourier operator. This frees the
algorithmic statement from the choice of basis input in `qftDeriv`. -/
theorem qftCirOp_apply_eq (n : ℕ) [NeZero n]
    (ψ : HS (QubitD n) (univ : Finset (QubitL n))) :
    qftCirOp n ψ
      = (qftOp n : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) ψ := by
  rw [qftCirOp_eq_qftOp n]

end Qhl.QFTTriple

namespace Qhl.QFTSource
open Finset QFTTriple
variable (n : ℕ) [NeZero n] (x : Fin n → Bool)

noncomputable def inputAssn : Assn (ℕ × ℕ) (QubitD n) :=
  Assn.ofState (prodV (QubitD n) (W := univ) (fun i => qbit (x i)))
    (norm_prodV_eq_one _ fun _ => norm_qbit _)
noncomputable def outputAssn : Assn (ℕ × ℕ) (QubitD n) :=
  Assn.ofState (fourierState n x) (norm_fourierState n x)



/-- Inner ladder invariant reads the outer counter and the fixed basis label. -/
theorem qftSub_deriv {φ : ℕ × ℕ → Prop}
    (hφ : ∀ σ v, φ ((CounterLens.snd ℕ).set σ v) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1 < n) :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ)
          (qftStageMidN n x σ.1))
        (fun σ : ℕ × ℕ => norm_prodV_eq_one _ (norm_qftStageMidN n x σ.1))) φ)
      (qftSub n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : ℕ × ℕ => prodV (QubitD n) (W := univ)
          (qftStageFam n x (σ.1 + 1)))
        (fun σ : ℕ × ℕ => norm_prodV_eq_one _ (norm_qftStageFam n x (σ.1 + 1)))) φ) := by
  refine SourceDerivTot.countedStateChainVar (CounterLens.snd ℕ)
    (fun σ => n - 1 - σ.1) φ hφ (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (qftLadderFamN n x σ.1 m))
    (fun m σ => norm_prodV_eq_one _ (norm_qftLadderFamN n x σ.1 m))
    (fun _ _ _ => rfl) ?_ ?_ ?_ ?_
  · intro σ _; exact congrArg _ (qftLadderFamN_zero n x σ.1)
  · intro σ hσ; exact congrArg _ (qftLadderFamN_full n x (hk σ hσ))
  · exact SourceDerivTot.countedRung_fam (ladReg n) (ladGate n) _ _
      fun σ hσ => ladder_action n x σ (hk σ hσ.1) hσ.2
  · intro z
    exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ) (hk σ hσ.1) hσ.2.1)).inj

/-- The outer stage loop, with an invariant indexed by the basis label. -/
theorem qftIter_deriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun _σ : ℕ × ℕ => prodV (QubitD n) (W := univ)
          (qftStageFam n x 0))
        (fun _σ : ℕ × ℕ => norm_prodV_eq_one _ (norm_qftStageFam n x 0))) fun _ => True)
      (qftIter n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun _σ : ℕ × ℕ => prodV (QubitD n) (W := univ)
          (qftStageFam n x n))
        (fun _σ : ℕ × ℕ =>
          norm_prodV_eq_one _ (norm_qftStageFam n x n))) fun _ => True) := by
  refine SourceDerivTot.countedStateChainVar (CounterLens.fst ℕ) (fun _ => n) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (qftStageFam n x m))
    (fun m σ => norm_prodV_eq_one _ (norm_qftStageFam n x m))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · refine SourceDerivTot.seq ?_ (qftSub_deriv n x
      (φ := fun σ => True ∧ σ.1 < n) (fun _ _ => Iff.rfl) (fun _ h => h.2))
    exact SourceDerivTot.countedRung_single_fam (hReg n) (hGate n)
      (fun σ => QFTTriple.ctrl n σ) (fun _ => H)
      (fun σ => norm_qftStageFam n x σ.1)
      (fun σ => norm_qftStageMidN n x σ.1)
      (fun σ _ => ⟨(Reg.single (QFTTriple.ctrl n σ)).inj, rfl⟩)
      (fun σ hσ => qftStageMidN_eq_update_H n x hσ.2)
  · intro z
    refine SourceDerivTot.seq
      (SourceDerivTot.unitary_identity (hReg n) (hGate n) _
        (fun σ _ => (Reg.single (QFTTriple.ctrl n σ)).inj)) ?_
    refine SourceDerivTot.countedIdentity (CounterLens.snd ℕ) (fun σ => n - 1 - σ.1) _
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) _ ?_ ?_
    · exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ) hσ.1.2.1 hσ.2)).inj
    · intro z'
      exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ) hσ.1.2.1 hσ.2.1)).inj

/-- The final reversal establishes the Fourier output ordering. -/
theorem revCirc_deriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun _σ : ℕ × ℕ => prodV (QubitD n) (W := univ)
          (qftRevFamN n x 0))
        (fun _σ : ℕ × ℕ => norm_prodV_eq_one _ (norm_qftRevFamN n x 0))) fun _ => True)
      (revCirc n)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun _σ : ℕ × ℕ => prodV (QubitD n) (W := univ)
          (qftRevFamN n x (n / 2)))
        (fun _σ : ℕ × ℕ =>
          norm_prodV_eq_one _ (norm_qftRevFamN n x (n / 2)))) fun _ => True) := by
  refine SourceDerivTot.countedStateChainVar (CounterLens.fst ℕ) (fun _ => n / 2) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prodV (QubitD n) (W := univ) (qftRevFamN n x m))
    (fun m σ => norm_prodV_eq_one _ (norm_qftRevFamN n x m))
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · exact SourceDerivTot.countedRung_pair_fam (swapReg n) (swapGate n)
      (fun σ => QFTTriple.ctrl n σ) (fun σ => QFTTriple.mir n σ)
      (fun σ hσ => QFTTriple.ctrl_ne_mir n (σ := σ) hσ.2) (fun _ => SWAP)
      (fun σ => norm_qftRevFamN n x σ.1)
      (fun σ => norm_qftRevFamN n x (σ.1 + 1))
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
        exact ⟨phaseKet (qftAngle x (n - 1 - σ.1)),
          phaseKet (qftAngle x σ.1),
          by rw [hc, hm, qftRevFamN_left n x hk, qftRevFamN_right n x hk, SWAP_vpair],
          by rw [hc, hm]; exact qftRevFamN_step n x hk⟩)
  · intro z
    exact SourceDerivTot.unitary_identity (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := σ) hσ.2.1)).inj

/-- A ladder preserves any classical predicate insensitive to its rung counter.
The identity quantum assertion makes this independent of the quantum input. -/
theorem qftSub_preserves {φ : ℕ × ℕ → Prop}
    (hφ : ∀ σ v, φ ((CounterLens.snd ℕ).set σ v) ↔ φ σ)
    (hk : ∀ σ, φ σ → σ.1 < n) :
    SourceDerivTot (SourceAssertion.ofAssn (Assn.one : Assn (ℕ × ℕ) (QubitD n)) φ) (qftSub n)
      (SourceAssertion.identity φ) := by
  refine SourceDerivTot.countedIdentity (CounterLens.snd ℕ) (fun σ => n - 1 - σ.1)
    φ hφ (fun _ _ => rfl) _ ?_ ?_
  · exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ) (hk σ hσ.1) hσ.2)).inj
  · intro z
    exact SourceDerivTot.unitary_identity (ladReg n) (ladGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_tgt n (σ := σ) (hk σ hσ.1) hσ.2.1)).inj

theorem qftDeriv : SourceDerivTot
    (SourceAssertion.ofAssn (inputAssn n x) (fun _ => True)) (qftCir n)
    (SourceAssertion.ofAssn (outputAssn n x) (fun _ => True)) := by
  refine SourceDerivTot.seq (SourceDerivTot.conseq ?_ (qftIter_deriv n x) ?_)
    (SourceDerivTot.conseq (SourceAssertion.entails_refl _) (revCirc_deriv n x) ?_)
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [inputAssn, Assn.ofState_op, Assn.ofStateFam_op, qftStageFam_zero]
      exact le_rfl
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [Assn.ofStateFam_op, qftRevFamN, qftRevFam_zero, qftStageFam_full]
      exact le_rfl
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [outputAssn, Assn.ofState_op, Assn.ofStateFam_op, qftRevFamN, qftRevFam_half]
      rw [fourierState_eq_prodV n x]
      simp only [revIdx_val]
      exact le_rfl

theorem qftValid : validTot (inputAssn n x) (qftCir n) (outputAssn n x) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (qftDeriv n x).sound

end Qhl.QFTSource
