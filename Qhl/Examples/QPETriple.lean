import Qhl.Logic.Source.PlacedStateChain
import Qhl.Logic.Source.ProductStateFam
import Qhl.Logic.ProductStateFam
import Qhl.Examples.ParallelHadamardTriple
import Qhl.Examples.InverseQFTTriple
import Qhl.Logic.CountedProdChain
import Qhl.Logic.SubroutineState
import Mathlib.Data.Nat.Pairing
import Qhl.Logic.Soundness
import Qhl.Gate.ControlledU
import Qhl.Register.Fourier

/-! # The quantum phase estimation triple (exact case)

CoqQ's phase-estimation case study (`src/example/coqq_paper/example.v:980-1035`,
`RS_QPE_exact`) in `QHL⁺_tot`, rendered as the standard **multi-qubit binary
QPE** on the `(n+1)`-qubit world: cells `0..n-1` (`Fin.castSucc k`) are the
counting register, cell `n` (`Fin.last n`) is the target qubit carrying an
eigenstate `ψ` of the single-qubit gate `U`, `U ψ = e^{2πiθ} ψ`. In the exact
case `θ = natVal x / 2^n` (CoqQ's hypothesis `a%:R = theta * n.+1%:R`), for
every width `n ≥ 1`, **every** bit vector `x`, every `U` and every unit
eigenstate `ψ`:

```
⊨ₜ { ∣0⟩^n ⊗ ∣ψ⟩ }  qpeCir n U  { ∣x⟩ ⊗ ∣ψ⟩ }.
```

**The loops are genuine `while` loops.** The printed system of the QHL⁺ paper
has no `for` rule, so both bounded loops of QPE are the counted `qWhile⁺` loop
`cnt := 0 ; while cnt < n do BODY ; cnt := cnt + 1 od` over the store `σT = ℕ`
(`CounterLens.nat`), discharged through the packaged rule
`DerivTot.countedProdChainSource` (`Qhl/Logic/CountedProdChain.lean`) — built from
the printed constructors only: (Ax-Ass), (R-Seq), (R-Conseq), **(R-Loop-tot)**
with ranking function `t σ = n - cnt`.

**The subroutines are LITERALLY reused** (the charter's §Subroutine REUSE):

* **Stage 1 is the imported parallel-Hadamard triple.** `phCtrl n` is the
  generic loop `ParallelHadamardTriple.phProgOn` at the counting register
  `ctrlReg n`, and its stage triple `phDeriv` is discharged by the **proved
  derivation `ParallelHadamardTriple.phDerivOn`**
  (`Qhl/Examples/ParallelHadamardTriple.lean` §5) at that placement — the
  eigenstate cell riding through as the frame — plus two (R-Conseq) endpoint
  recasts (`mem_sig_ctrlReg`). No Hadamard-loop content is derived here.
* **Stage 2** (the kickback, whose passes share the target wire) is one
  `DerivTot.countedProdChainSource` call along the library invariant `qpeKickFam`;
  each pass is one two-cell rung (`DerivTot.countedRung_pair`) whose action
  facts are the phase kickback `control_pow_vpair_phaseKet`
  (`Qhl/Gate/ControlledU.lean`) and the exact-case arithmetic `phaseKet_kick`
  (`Qhl/Register/Fourier.lean` §11).
* **Stage 3 consumes the verified inverse-QFT derivation.**
  `InverseQFTTriple.iqftRevDeriv` is transported to the natural-number store
  by `DerivTot.mapStore_pull`, using `Nat.pair` and `Nat.unpair` to encode its
  two counters. `DerivTot.onReg_prodA` then places the entire circuit on the
  counting register and frames the target eigenstate. Both transport rules
  are derived from the existing `DerivTot` constructors. The readout program
  contains the inverse-QFT circuit's counted `while` loops and elementary
  gates; it does not replace them by a whole-register operator.

| here | CoqQ (`example.v`) |
|---|---|
| `phCtrl` | `[ut x := 'Hn]` (`:1003`) — uniform superposition on the counting register |
| `kickCir` | `[ut (x,y) := Uf]`, `Uf = Multiplexer (U ^+ i)` (`:997-1004`) |
| `iqftCtrl` | `[ut x := IQFT]` (`:1005`) |
| `qpeCir` | `QPE` (`:1001`) |
| `hU` | `eigU` (`:984`) + exactness (`:1030`) |
| `qpeDeriv`/`qpeValid` | `RS_QPE_exact` (`:1029`) |

CoqQ opens with the initialisation `[it x := 0]`; here the all-zeros counting
register is part of the precondition instead — the same non-vacuous input
state. Two outer stages followed by the inverse-QFT circuit, **no example-level
induction**. Soundness is wired by `qpeValid`; both endpoint assertions are
projector effects `∣·⟩⟨·∣` over the density-matrix semantics, store-constant
over `σT = ℕ`, so the triple holds at an arbitrary initial counter value (each
loop initialises its own counter).
-/

namespace Qhl.QPETriple

open Finset

/-! ## §1. The registers of the `(n+1)`-qubit world -/

/-- The counting cells lie strictly below the target. -/
theorem castSucc_ne_last {n : ℕ} (k : Fin n) : k.castSucc ≠ Fin.last n :=
  Fin.ne_of_lt (Fin.castSucc_lt_last k)

/-- The **counting register**: cells `0..n-1` of the `(n+1)`-qubit world, in
order. CoqQ's control register `x` of `'QReg['I_n * T]` (`example.v:987`). -/
noncomputable def ctrlReg (n : ℕ) : Reg (QubitL (n + 1)) n :=
  ⟨Fin.castSucc, Fin.castSucc_injective n⟩

/-- A cell lies in the counting register iff its index is below `n`. -/
theorem mem_sig_ctrlReg {n : ℕ} {i : Fin (n + 1)} :
    i ∈ (ctrlReg n).sig ↔ (i : ℕ) < n := by
  rw [Reg.mem_sig]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro h
    exact ⟨⟨(i : ℕ), h⟩, Fin.ext rfl⟩

/-- The full register of the IQFT's own `n`-qubit world (as in
`Qhl/Examples/InverseQFTTriple.lean`). -/
noncomputable def fullRegN (n : ℕ) : Reg (QubitL n) n := Reg.ofEquiv (Equiv.refl (Fin n))

/-- Operator form retained for the legacy approximate-QPE examples. The exact
QPE circuit below instead reuses `iqftRevCir` and its Hoare derivation.
**The inverse QFT as a gate of the counting block**: `iqftOp n` (§10, CoqQ
`IQFT`) through `Reg.fullGate` — the tuple space of `ctrlReg n` **is**
definitionally that of the full `n`-qubit register, so no cast is needed. -/
noncomputable def iqftGate (n : ℕ) : UnitaryOp (TSpace (QubitD (n + 1)) (ctrlReg n).toFun) :=
  (fullRegN n).fullGate (QubitD n) (Reg.sig_ofEquiv _) (iqftOp n)

/-- Placement of the IQFT's qubits on the counting register. -/
def ctrlEmb (n : ℕ) : QubitL n ↪ QubitL (n + 1) :=
  ⟨Fin.castSucc, Fin.castSucc_injective n⟩

/-- Encode the IQFT's two local counters in QPE's natural-number store. -/
def iqftStore : StoreLens ℕ (ℕ × ℕ) where
  get := Nat.unpair
  put := fun _ s => Nat.pair s.1 s.2

/-! ## §2. The store-read counting cell (the library `cell`, `castSucc`-ed) -/

/-- The cell the loops touch: the `cell n σ`-th counting cell of the
`(n+1)`-qubit world; the target `Fin.last n` is never named by either loop. -/
def qpeCell (n : ℕ) [NeZero n] (σ : ℕ) : Fin (n + 1) := (cell n σ).castSucc

/-- The loops never name the target cell. -/
theorem qpeCell_ne_last (n : ℕ) [NeZero n] (σ : ℕ) : qpeCell n σ ≠ Fin.last n :=
  castSucc_ne_last (cell n σ)

/-- Below the loop bound the store-read cell is the `σ`-th counting cell. -/
theorem qpeCell_of_lt (n : ℕ) [NeZero n] {σ : ℕ} (hσ : σ < n) :
    qpeCell n σ = (⟨σ, hσ⟩ : Fin n).castSucc :=
  congrArg Fin.castSucc (cell_eq_mk n hσ)

/-! ## §3. The programs (CoqQ `QPE`, `example.v:1001-1005`) -/

/-- The preparation body's register expression: the store-read counting cell. -/
def phRegE (n : ℕ) [NeZero n] : RegExpr ℕ (QubitL (n + 1)) 1 :=
  fun σ => (Reg.single (qpeCell n σ)).toFun

/-- The Hadamard on the store-read counting cell. -/
noncomputable def phGate (n : ℕ) [NeZero n] (σ : ℕ) :
    UnitaryOp (TSpace (QubitD (n + 1)) (phRegE n σ)) :=
  singleGate (QubitD (n + 1)) (qpeCell n σ) H

/-- **The uniform-superposition stage** — CoqQ `[ut x := 'Hn]` (`:1003`): the
counted loop `cnt := 0 ; while cnt < n do q[cnt] *= H ; cnt := cnt + 1 od`. -/
noncomputable def phCtrl (n : ℕ) [NeZero n] : Prog ℕ (QubitD (n + 1)) :=
  countedProg CounterLens.nat (fun _ => n) (.unitary 1 (phRegE n) (phGate n))

/-- The kickback body's register expression: the store-read counting cell
(control) paired with the target (eigenstate). -/
def kickRegE (n : ℕ) [NeZero n] : RegExpr ℕ (QubitL (n + 1)) 2 :=
  fun σ => (Reg.pair (qpeCell n σ) (Fin.last n) (qpeCell_ne_last n σ)).toFun

/-- The controlled power `U^{2^{n-1-cnt}}` on that pair; big-endian: bit `k`
has weight `2^{n-1-k}`. -/
noncomputable def kickGate (n : ℕ) [NeZero n] (U : UnitaryOp 𝕢) (σ : ℕ) :
    UnitaryOp (TSpace (QubitD (n + 1)) (kickRegE n σ)) :=
  pairGate (qpeCell n σ) (Fin.last n) (qpeCell_ne_last n σ) (control (U ^ 2 ^ (n - 1 - σ)))

/-- **The phase-kickback stage** — CoqQ `[ut (x,y) := Uf]`,
`Uf = Multiplexer (fun i => U ^+ i)` (`:997-1004`): the counted `while` loop of
the controlled powers. The passes **share the target wire**, so the loop
invariant is the sequential family `qpeKickFam`. -/
noncomputable def kickCir (n : ℕ) [NeZero n] (U : UnitaryOp 𝕢) : Prog ℕ (QubitD (n + 1)) :=
  countedProg CounterLens.nat (fun _ => n) (.unitary 2 (kickRegE n) (kickGate n U))

/-- The readout stage runs the verified inverse-QFT circuit on the counting
register, with its two counters encoded in the natural-number store. -/
noncomputable def iqftCtrl (n : ℕ) [NeZero n] : Prog ℕ (QubitD (n + 1)) :=
  ((InverseQFTTriple.iqftRevCir n).mapStore iqftStore).onReg (ctrlEmb n)

/-- **CoqQ `QPE`** (`example.v:1001`): uniform superposition, kickback, inverse
QFT. The first two stages and the inverse-QFT circuit use counted `while`
loops; no measurement. -/
noncomputable def qpeCir (n : ℕ) [NeZero n] (U : UnitaryOp 𝕢) : Prog ℕ (QubitD (n + 1)) :=
  (phCtrl n).seq ((kickCir n U).seq (iqftCtrl n))

/-! ## §4. The stage triples -/

section Triple

variable (n : ℕ) [NeZero n] (x : Fin n → Bool) (U : UnitaryOp 𝕢) (ψ : 𝕢) (hψ : ‖ψ‖ = 1)

/- The exact-case eigenstate hypothesis: `U ψ = e^{2πi·(natVal x/2^n)} ψ` —
CoqQ `eigU` (`example.v:984`) at the exactness `a%:R = theta * n.+1%:R`
(`:1030`). -/
variable (hU : (U : 𝕢 →ₗ[ℂ] 𝕢) ψ
    = Complex.exp (((2 * Real.pi * ((natVal x : ℝ) / 2 ^ n) : ℝ) : ℂ) * Complex.I) • ψ)

/-- **Stage 1** — `{∣0⟩^n ⊗ ψ} phCtrl {(∣+⟩^n ⊗ ψ) ∧ cnt = n}`: the **imported
parallel-Hadamard derivation** `ParallelHadamardTriple.phDerivOn`
(`Qhl/Examples/ParallelHadamardTriple.lean` §5), consumed at the counting
register `ctrlReg n` of the `(n+1)`-qubit world with the eigenstate `ψ` as the
frame on the target cell — `phCtrl n` **is** the generic loop `phProgOn` at
that placement, so the proved subroutine discharges the stage; the two
(R-Conseq) endpoint recasts identify `phFamOn`'s endpoints with
`qpeInitFam`/`qpePlusFam` through `mem_sig_ctrlReg`. No Hadamard-loop content
is re-derived here. -/
theorem phDeriv :
    DerivTot (σT := ℕ)
      (prodA (QubitD (n + 1)) (qpeInitFam n ψ) (norm_qpeInitFam n ψ hψ))
      (phCtrl n)
      ((prodA (QubitD (n + 1)) (qpePlusFam n ψ) (norm_qpePlusFam n ψ hψ)).mask
        fun σ => σ = n) := by
  have h0 : qpeInitFam n ψ
      = ParallelHadamardTriple.phFamOn n (ctrlReg n) (fun _ => ψ) 0 := by
    rw [ParallelHadamardTriple.phFamOn_zero]
    funext i
    by_cases h : (i : ℕ) < n
    · rw [if_pos (mem_sig_ctrlReg.mpr h)]
      simp only [qpeInitFam]
      rw [if_pos h]
    · rw [if_neg fun hc => h (mem_sig_ctrlReg.mp hc)]
      simp only [qpeInitFam]
      rw [if_neg h]
  have h1 : ParallelHadamardTriple.phFamOn n (ctrlReg n) (fun _ => ψ) n
      = qpePlusFam n ψ := by
    rw [ParallelHadamardTriple.phFamOn_full]
    funext i
    by_cases h : (i : ℕ) < n
    · rw [if_pos (mem_sig_ctrlReg.mpr h)]
      simp only [qpePlusFam]
      rw [if_pos h]
    · rw [if_neg fun hc => h (mem_sig_ctrlReg.mp hc)]
      simp only [qpePlusFam]
      rw [if_neg h]
  exact DerivTot.conseq (prodA_le h0)
    (ParallelHadamardTriple.phDerivOn n (ctrlReg n) CounterLens.nat
      (fun _ => ψ) (fun _ => hψ))
    (Assn.mask_le_mask (fun _ h => h)
      fun σ _ => le_of_eq (by rw [prodA_op, prodA_op, h1]))

include hU in
/-- **Stage 2** — `{∣+⟩^n ⊗ ψ} kickCir {(fourierState x ⊗ ψ) ∧ cnt = n}` (in
product form): ONE call of the packaged counted-loop rule along the library
invariant `qpeKickFam`; each pass is one two-cell rung
(`DerivTot.countedRung_pair`) whose action facts are the library phase kickback
`control_pow_vpair_phaseKet`, the exact-case arithmetic `phaseKet_kick` and
`qpeKickFam_step`. -/
theorem kickDeriv :
    DerivTot (σT := ℕ)
      (prodA (QubitD (n + 1)) (qpePlusFam n ψ) (norm_qpePlusFam n ψ hψ))
      (kickCir n U)
      ((prodA (QubitD (n + 1)) (qpePhasedFam n x ψ) (norm_qpePhasedFam n x ψ hψ)).mask
        fun σ => σ = n) :=
  DerivTot.countedProdChainSource CounterLens.nat
    (qpeKickFam n x ψ) (norm_qpeKickFam n x ψ hψ)
    (qpeKickFam_zero n x ψ) (qpeKickFam_full n x ψ)
    (DerivTot.countedRung_pair_fam (kickRegE n) (kickGate n U)
      (qpeCell n) (fun _ => Fin.last n) (fun σ _ => qpeCell_ne_last n σ)
      (fun σ => control (U ^ 2 ^ (n - 1 - σ)))
      (fun σ => norm_qpeKickFam n x ψ hψ σ)
      (fun σ => norm_qpeKickFam n x ψ hψ (σ + 1))
      (fun σ _ => ⟨(Reg.pair _ _ (qpeCell_ne_last n σ)).inj, rfl⟩)
      (fun σ hσ => by
        change σ < n at hσ
        refine ⟨phaseKet (qftAngle x (n - 1 - σ)), ψ, ?_, ?_⟩
        · have hctrl : qpeKickFam n x ψ σ (qpeCell n σ) = qplus := by
            rw [qpeCell_of_lt n hσ]
            exact qpeKickFam_ctrl n x ψ ⟨σ, hσ⟩
          rw [hctrl, qpeKickFam_last n x ψ σ, ← phaseKet_zero,
            control_pow_vpair_phaseKet U hU (2 ^ (n - 1 - σ)) 0, zero_add,
            phaseKet_kick n x (show n - 1 - σ < n by omega)]
        · rw [qpeCell_of_lt n hσ]
          exact qpeKickFam_step n x ψ ⟨σ, hσ⟩))
    (fun _ => DerivTot.unitary_identity_mask (kickRegE n) (kickGate n U)
      (fun σ _ => (Reg.pair _ _ (qpeCell_ne_last n σ)).inj))

/-- Stage 3 reuses the inverse-QFT Hoare derivation, transported along the
counter encoding and framed by the target eigenstate. -/
theorem iqftCtrlDeriv :
    DerivTot (σT := ℕ)
      (prodA (QubitD (n + 1)) (qpePhasedFam n x ψ) (norm_qpePhasedFam n x ψ hψ))
      (iqftCtrl n)
      (prodA (QubitD (n + 1)) (qpeOutFam n x ψ) (norm_qpeOutFam n x ψ hψ)) := by
  apply DerivTot.onReg_prodA (ctrlEmb n)
    (qpePhasedFam n x ψ) (qpeOutFam n x ψ)
    (norm_qpePhasedFam n x ψ hψ) (norm_qpeOutFam n x ψ hψ)
  · intro i hi
    have hns : ¬ (i : ℕ) < n := by
      intro hc
      exact (mem_sdiff.mp hi).2 (mem_map.mpr
        ⟨⟨i.val, hc⟩, mem_univ _, Fin.ext rfl⟩)
    have heq : i = Fin.last n := Fin.ext (by have := i.isLt; simp; omega)
    subst i
    rw [qpePhasedFam_last, qpeOutFam_last]
  · have hd := DerivTot.mapStore_pull iqftStore
      (fun _ s => Nat.unpair_pair s.1 s.2) (InverseQFTTriple.iqftRevDeriv n x)
    refine DerivTot.conseq ?_ hd ?_
    · intro σ
      apply le_of_eq
      simp only [prodA_op, Assn.pull_op, Assn.ofState_op, fourierState_eq_prodV]
      congr 1 <;> apply congrArg (prodV (QubitD n)) <;> funext j
        <;> exact qpePhasedFam_castSucc n x ψ j
    · intro σ
      apply le_of_eq
      simp only [prodA_op, Assn.pull_op, Assn.ofState_op]
      congr 1 <;> apply congrArg (prodV (QubitD n)) <;> funext j
        <;> exact (qpeOutFam_castSucc n x ψ j).symm

/-! ## §5. The QPE triple (CoqQ `RS_QPE_exact`) -/

include hU in
/-- **The QPE derivation** — CoqQ `RS_QPE_exact` (`example.v:1029`). For every
width `n ≥ 1`, every bit vector `x`, every single-qubit `U` and every unit
eigenstate `ψ` with `U ψ = e^{2πi·(natVal x/2^n)} ψ`:

```
⊢ₜ { ∣0⟩^n ⊗ ∣ψ⟩ }  qpeCir n U  { ∣x⟩ ⊗ ∣ψ⟩ }.
```

(R-Seq) of the three stage triples, an (R-Conseq) at each loop exit dropping
the counter mask; nothing else. -/
theorem qpeDeriv :
    DerivTot (σT := ℕ)
      (prodA (QubitD (n + 1)) (qpeInitFam n ψ) (norm_qpeInitFam n ψ hψ))
      (qpeCir n U)
      (prodA (QubitD (n + 1)) (qpeOutFam n x ψ) (norm_qpeOutFam n x ψ hψ)) :=
  DerivTot.seq (phDeriv n ψ hψ)
    (DerivTot.seq
      (DerivTot.conseq (Assn.mask_le_of_imp_le fun _ _ => le_rfl)
        (kickDeriv n x U ψ hψ hU) (Assn.le_refl' _))
      (DerivTot.conseq (Assn.mask_le_of_imp_le fun _ _ => le_rfl)
        (iqftCtrlDeriv n x ψ hψ) (Assn.le_refl' _)))

include hU in
/-- **The QPE triple, semantically** — `qpeDeriv` through soundness: for
**every** density operator and every initial counter value, the expectation of
the projector effect `∣0…0, ψ⟩⟨0…0, ψ∣` bounds the terminal expectation of
`∣x, ψ⟩⟨x, ψ∣`. -/
theorem qpeValid :
    validTot (σT := ℕ)
      (prodA (QubitD (n + 1)) (qpeInitFam n ψ) (norm_qpeInitFam n ψ hψ))
      (qpeCir n U)
      (prodA (QubitD (n + 1)) (qpeOutFam n x ψ) (norm_qpeOutFam n x ψ hψ)) :=
  (qpeDeriv n x U ψ hψ hU).sound

omit [NeZero n] in
/-- **Non-vacuity of the readout**: on every counting wire the postcondition is
literally the basis ket of the bit of `x` — the measurement-free readout of the
phase (library `qpeOutFam_castSucc`). -/
theorem qpeOut_readout (j : Fin n) : qpeOutFam n x ψ j.castSucc = qbit (x j) :=
  qpeOutFam_castSucc n x ψ j

end Triple

/-- **Non-vacuity of the postcondition, closed form**: when the eigenstate is
itself a basis ket, the postcondition is the full computational basis state
(CoqQ `t2tv_tuple`), hence in particular a nonzero effect; together with
`norm_prodV_eq_one` at the precondition the triple is genuine in both
directions. -/
theorem prodV_qpeOutFam_eq_deltav (n : ℕ) (x : Fin n → Bool) (b : Bool) :
    prodV (QubitD (n + 1)) (W := (univ : Finset (QubitL (n + 1))))
        (qpeOutFam n x (qbit b))
      = deltav (QubitD (n + 1))
          (fun i : ↥(univ : Finset (QubitL (n + 1))) =>
            if h : ((i : QubitL (n + 1)) : ℕ) < n then x ⟨_, h⟩ else b) := by
  have h : qpeOutFam n x (qbit b)
      = fun i : Fin (n + 1) =>
          EuclideanSpace.single (if h : (i : ℕ) < n then x ⟨(i : ℕ), h⟩ else b) 1 := by
    funext i
    by_cases h : (i : ℕ) < n
    · rw [qpeOutFam, dif_pos h, dif_pos h]
      rfl
    · rw [qpeOutFam, dif_neg h, dif_neg h]
      rfl
  rw [h]
  exact prodV_single (QubitD (n + 1)) _

end Qhl.QPETriple

namespace Qhl.InverseQFTPlacedSource
open Finset QPETriple SourceDerivTot
namespace Literal
open QFTTriple InverseQFTTriple
variable (n : ℕ) [NeZero n] (x : Fin n → Bool)
variable (R : EndM (QubitD (n + 1)) (univ \ embRange (ctrlEmb n))) (hR : IsEffect R)

def stageCounter : CounterLens ℕ :=
  (CounterLens.fst ℕ).pullback QPETriple.iqftStore (fun _ s => Nat.unpair_pair s.1 s.2)
def rungCounter : CounterLens ℕ :=
  (CounterLens.snd ℕ).pullback QPETriple.iqftStore (fun _ s => Nat.unpair_pair s.1 s.2)
def swapReg : RegExpr ℕ (QubitL n) 2 :=
  fun σ => QFTTriple.swapReg n (Nat.unpair σ)
noncomputable def swapGate (σ : ℕ) := QFTTriple.swapGate n (Nat.unpair σ)
def ihReg : RegExpr ℕ (QubitL n) 1 :=
  fun σ => InverseQFTTriple.ihReg n (Nat.unpair σ)
noncomputable def ihGate (σ : ℕ) := InverseQFTTriple.ihGate n (Nat.unpair σ)
def iladReg : RegExpr ℕ (QubitL n) 2 :=
  fun σ => InverseQFTTriple.iladReg n (Nat.unpair σ)
noncomputable def iladGate (σ : ℕ) := InverseQFTTriple.iladGate n (Nat.unpair σ)
noncomputable def revCirc : Prog ℕ (QubitD (n + 1)) :=
  ((QFTTriple.revCirc n).mapStore QPETriple.iqftStore).onReg (ctrlEmb n)
noncomputable def iqftSub : Prog ℕ (QubitD (n + 1)) :=
  ((InverseQFTTriple.iqftSub n).mapStore QPETriple.iqftStore).onReg (ctrlEmb n)
noncomputable def iqftIter : Prog ℕ (QubitD (n + 1)) :=
  ((InverseQFTTriple.iqftIter n).mapStore QPETriple.iqftStore).onReg (ctrlEmb n)
/-- The backward reversal reads the stored array in its invariant. -/
theorem revCircBack_deriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (framedFam (ctrlEmb n) R hR (fun σ : ℕ => prodV
        (QubitD n) (W := univ)
          (iqftRevFamN n x 0))
        (fun σ : ℕ => norm_prodV_eq_one _ (norm_iqftRevFamN n x 0)))
        fun _ => True)
      (revCirc n)
      (SourceAssertion.ofAssn (framedFam (ctrlEmb n) R hR (fun σ : ℕ => prodV
        (QubitD n) (W := univ)
          (iqftRevFamN n x (n / 2)))
        (fun σ : ℕ =>
          norm_prodV_eq_one _ (norm_iqftRevFamN n x (n / 2)))) fun _ => True) := by
  refine framedCounted (ctrlEmb n) R hR stageCounter (fun _ => n / 2) (fun _ => True)
    (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPETriple.iqftStore, CounterLens.fst,
        CounterLens.snd, CounterLens.fst, CounterLens.snd]) (by intros; simp
        [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPETriple.iqftStore, CounterLens.fst,
        CounterLens.snd, CounterLens.fst, CounterLens.snd])
    (fun m σ => prodV (QubitD n) (W := univ) (iqftRevFamN n x m))
    (fun m σ => norm_prodV_eq_one _ (norm_iqftRevFamN n x m))
    (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPETriple.iqftStore, CounterLens.fst,
        CounterLens.snd, CounterLens.fst, CounterLens.snd]) (by intros; simp
        [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPETriple.iqftStore, CounterLens.fst,
        CounterLens.snd, CounterLens.fst, CounterLens.snd]) (by intros; simp
        [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPETriple.iqftStore, CounterLens.fst,
        CounterLens.snd, CounterLens.fst, CounterLens.snd]) ?_ ?_
  · exact framedPair (ctrlEmb n) R hR (swapReg n) (swapGate n)
      (fun σ => QFTTriple.ctrl n (Nat.unpair σ)) (fun σ => QFTTriple.mir n (Nat.unpair σ))
      (fun σ hσ => QFTTriple.ctrl_ne_mir n (σ := Nat.unpair σ) hσ.2) (fun _ => SWAP)
      (fun σ => norm_iqftRevFamN n x (Nat.unpair σ).1)
      (fun σ => norm_iqftRevFamN n x ((Nat.unpair σ).1 + 1))
      (fun σ hσ => by
        have hne := QFTTriple.ctrl_ne_mir n (σ := Nat.unpair σ) hσ.2
        refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
        change regLift (D := QubitD n)
          ⟨QFTTriple.swapReg n (Nat.unpair σ), (Reg.pair _ _ hne).inj⟩
          (QFTTriple.swapGate n (Nat.unpair σ)) =
          regLift (D := QubitD n)
            (Reg.pair (QFTTriple.ctrl n (Nat.unpair σ)) (QFTTriple.mir n (Nat.unpair σ)) hne)
            (pairGate (D := QubitD n)
              (QFTTriple.ctrl n (Nat.unpair σ)) (QFTTriple.mir n (Nat.unpair σ)) hne SWAP)
        rw [show QFTTriple.swapGate n (Nat.unpair σ) = pairGate (D := QubitD n)
            (QFTTriple.ctrl n (Nat.unpair σ)) (QFTTriple.mir n (Nat.unpair σ)) hne SWAP
        from by
          simp only [QFTTriple.swapGate]; rw [dif_pos hne]]
        rfl)
      (fun σ hσ => by
        have hk : (Nat.unpair σ).1 < n / 2 := hσ.2
        have hc : QFTTriple.ctrl n (Nat.unpair σ) = cell n (Nat.unpair σ).1 := rfl
        have hm : QFTTriple.mir n (Nat.unpair σ) = cell n (n - 1 - (Nat.unpair σ).1) := rfl
        exact ⟨phaseKet (qftAngle x (Nat.unpair σ).1),
          phaseKet (qftAngle x (n - 1 - (Nat.unpair σ).1)),
          by rw [hc, hm, iqftRevFamN_left n x hk, iqftRevFamN_right n x hk, SWAP_vpair],
          by rw [hc, hm]; exact iqftRevFamN_step n x hk⟩)
  · intro z
    exact framedIdentity (ctrlEmb n) (swapReg n) (swapGate n) _ fun σ hσ =>
      (Reg.pair _ _ (QFTTriple.ctrl_ne_mir n (σ := Nat.unpair σ) hσ.2.1)).inj

/-- The inverse controlled-phase gate advances the decreasing ladder family. -/
private theorem iladder_action (σ : ℕ) (hk : (Nat.unpair σ).1 < n)
        (hj : (Nat.unpair σ).2 < (Nat.unpair σ).1) :
    ∃ hinj : Function.Injective (iladReg n σ),
      regLift (D := QubitD n) ⟨iladReg n σ, hinj⟩ (iladGate n σ)
        (prodV (QubitD n) (W := univ)
          (qftLadderFamN n x (n - 1 - (Nat.unpair σ).1) ((Nat.unpair σ).1 - (Nat.unpair σ).2))) =
        prodV (QubitD n) (W := univ)
          (qftLadderFamN n x (n - 1 - (Nat.unpair σ).1) ((Nat.unpair σ).1 - ((Nat.unpair σ).2 +
        1))) := by
  have hne : InverseQFTTriple.ictrl n (Nat.unpair σ) ≠ InverseQFTTriple.itgt n (Nat.unpair σ) :=
    InverseQFTTriple.ictrl_ne_itgt n (σ := Nat.unpair σ) hk hj
  refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
  rw [show regLift (D := QubitD n) ⟨iladReg n σ, (Reg.pair _ _ hne).inj⟩ (iladGate n σ)
      = regLift (D := QubitD n)
          (Reg.pair (InverseQFTTriple.ictrl n (Nat.unpair σ)) (InverseQFTTriple.itgt n
        (Nat.unpair σ)) hne)
          (pairGate (D := QubitD n) (InverseQFTTriple.ictrl n (Nat.unpair σ))
        (InverseQFTTriple.itgt n (Nat.unpair σ)) hne
            (cphase (-(2 * Real.pi / 2 ^ ((Nat.unpair σ).1 - 1 - (Nat.unpair σ).2 + 2)))))
        from by
    rw [show iladGate n σ = pairGate (D := QubitD n)
        (InverseQFTTriple.ictrl n (Nat.unpair σ)) (InverseQFTTriple.itgt n (Nat.unpair σ)) hne
        (cphase (-(2 * Real.pi / 2 ^ ((Nat.unpair σ).1 - 1 - (Nat.unpair σ).2 + 2)))) from by
      change InverseQFTTriple.iladGate n (Nat.unpair σ) = _
      simp only [InverseQFTTriple.iladGate]; rw [dif_pos hne]]
    rfl]
  exact regLift_cphase_neg_qftLadderFamN n x hk hj hne


theorem iqftSub_current {φ : ℕ → Prop}
    (hφ : ∀ σ v, φ (rungCounter.set σ v) ↔ φ σ)
    (hk : ∀ σ, φ σ → (Nat.unpair σ).1 < n) :
    SourceDerivTot
      (SourceAssertion.ofAssn (framedFam (ctrlEmb n) R hR (fun σ : ℕ =>
        prodV (QubitD n) (W := univ) (qftStageFam n x (n - (Nat.unpair σ).1)))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n x (n - (Nat.unpair σ).1)))) φ)
      (iqftSub n)
      (SourceAssertion.ofAssn (framedFam (ctrlEmb n) R hR (fun σ : ℕ =>
        prodV (QubitD n) (W := univ) (qftStageMidN n x (n - 1 - (Nat.unpair σ).1)))
        (fun σ => norm_prodV_eq_one _
          (norm_qftStageMidN n x (n - 1 - (Nat.unpair σ).1)))) φ) := by
    refine framedCounted (ctrlEmb n) R hR rungCounter
      (fun σ => (Nat.unpair σ).1) φ hφ (by intros; simp [stageCounter, rungCounter,
        CounterLens.pullbackFst, CounterLens.pullback, StoreLens.fst,
        QPETriple.iqftStore, CounterLens.fst,
        CounterLens.snd, CounterLens.fst, CounterLens.snd])
      (fun m σ => prodV (QubitD n) (W := univ)
        (qftLadderFamN n x (n - 1 - (Nat.unpair σ).1) ((Nat.unpair σ).1 - m)))
      (fun m σ => norm_prodV_eq_one _
        (norm_qftLadderFamN n x (n - 1 - (Nat.unpair σ).1) ((Nat.unpair σ).1 - m)))
      (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst, QPETriple.iqftStore,
        CounterLens.fst, CounterLens.snd, CounterLens.fst,
        CounterLens.snd]) ?_ ?_ ?_ ?_
    · intro σ hσ
      apply congrArg
      have hlt := hk σ hσ
      calc
        qftLadderFamN n x (n - 1 - (Nat.unpair σ).1) ((Nat.unpair σ).1 - 0) =
            qftLadderFamN n x (n - 1 - (Nat.unpair σ).1) (n - 1 - (n - 1 - (Nat.unpair σ).1))
        := by
          congr 1
          omega
        _ = qftStageFam n x ((n - 1 - (Nat.unpair σ).1) + 1) :=
          qftLadderFamN_full n x (by omega)
        _ = qftStageFam n x (n - (Nat.unpair σ).1) := by congr 1; omega
    · intro σ _
      rw [Nat.sub_self]
      exact congrArg _ (qftLadderFamN_zero n x (n - 1 - (Nat.unpair σ).1))
    · exact framedRung (ctrlEmb n) R hR (iladReg n) (iladGate n) _ _
        fun σ hσ => iladder_action n x σ (hk σ hσ.1) hσ.2
    · intro z
      exact framedIdentity (ctrlEmb n) (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := Nat.unpair σ) (hk σ hσ.1)
        hσ.2.1)).inj

/-- Reverse stages use the QFT stage family at the decreasing index. -/
theorem iqftIter_deriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (framedFam (ctrlEmb n) R hR (fun σ : ℕ => prodV
        (QubitD n) (W := univ)
          (qftStageFam n x n))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n x n))) fun _ => True)
      (iqftIter n)
      (SourceAssertion.ofAssn (framedFam (ctrlEmb n) R hR (fun σ : ℕ => prodV
        (QubitD n) (W := univ)
          (qftStageFam n x 0))
        (fun σ => norm_prodV_eq_one _ (norm_qftStageFam n x 0))) fun _ => True) := by
  refine framedCounted (ctrlEmb n) R hR stageCounter (fun _ => n) (fun _ => True)
    (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPETriple.iqftStore, CounterLens.fst,
        CounterLens.snd, CounterLens.fst, CounterLens.snd]) (by intros; simp
        [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPETriple.iqftStore, CounterLens.fst,
        CounterLens.snd, CounterLens.fst, CounterLens.snd])
    (fun m σ => prodV (QubitD n) (W := univ) (qftStageFam n x (n - m)))
    (fun m σ => norm_prodV_eq_one _ (norm_qftStageFam n x (n - m)))
    (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPETriple.iqftStore, CounterLens.fst,
        CounterLens.snd, CounterLens.fst, CounterLens.snd]) (by intros; simp
        [stageCounter, rungCounter, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, QPETriple.iqftStore, CounterLens.fst,
        CounterLens.snd, CounterLens.fst, CounterLens.snd]) (fun _ _ => by rw
        [Nat.sub_self]) ?_ ?_
  · refine SourceDerivTot.seq (iqftSub_current n x R hR
      (φ := fun σ => True ∧ (Nat.unpair σ).1 < n) (by intros; simp [stageCounter,
        rungCounter, CounterLens.pullbackFst, CounterLens.pullback, StoreLens.fst,
        QPETriple.iqftStore, CounterLens.fst,
        CounterLens.snd, CounterLens.fst, CounterLens.snd]) (fun _ h => h.2)) ?_
    exact framedSingle (ctrlEmb n) R hR (ihReg n) (ihGate n)
      (fun σ => InverseQFTTriple.ictrl n (Nat.unpair σ)) (fun _ => H)
      (fun σ => norm_qftStageMidN n x (n - 1 - (Nat.unpair σ).1))
      (fun σ => norm_qftStageFam n x (n - ((Nat.unpair σ).1 + 1)))
      (fun σ _ => ⟨(Reg.single (InverseQFTTriple.ictrl n (Nat.unpair σ))).inj, rfl⟩)
      (fun σ hσ => by
        change Function.update _ (cell n (n - 1 - (Nat.unpair σ).1)) _ = _
        rw [show n - ((Nat.unpair σ).1 + 1) = n - 1 - (Nat.unpair σ).1 from by omega]
        exact qftStageMidN_step_H n x (by have h := hσ.2; omega))
  · intro z
    refine SourceDerivTot.seq ?_
      (framedIdentity (ctrlEmb n) (ihReg n) (ihGate n) _
        (fun σ _ => (Reg.single (InverseQFTTriple.ictrl n (Nat.unpair σ))).inj))
    refine SourceDerivTot.countedIdentity rungCounter (fun σ => (Nat.unpair σ).1) _
      (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst, QPETriple.iqftStore,
        CounterLens.fst, CounterLens.snd, CounterLens.fst,
        CounterLens.snd]) (by intros; simp [stageCounter, rungCounter, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst, QPETriple.iqftStore,
        CounterLens.fst, CounterLens.snd, CounterLens.fst,
        CounterLens.snd]) _ ?_ ?_
    · exact framedIdentity (ctrlEmb n) (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := Nat.unpair σ) hσ.1.2.1 hσ.2)).inj
    · intro z'
      exact framedIdentity (ctrlEmb n) (iladReg n) (iladGate n) _ fun σ hσ =>
        (Reg.pair _ _ (InverseQFTTriple.ictrl_ne_itgt n (σ := Nat.unpair σ) hσ.1.2.1
        hσ.2.1)).inj


/-- The literal mapped inverse circuit at framed product-state endpoints. -/
theorem iqftProdDeriv :
    SourceDerivTot
      (SourceAssertion.ofAssn
        ((prodA (σT := ℕ) (QubitD n)
          (fun i => phaseKet (qftAngle x (n - 1 - (i : ℕ))))
          (fun _ => norm_phaseKet _)).embFrame (emb := ctrlEmb n) R hR) (fun _ => True))
      (QPETriple.iqftCtrl n)
      (SourceAssertion.ofAssn
        ((prodA (σT := ℕ) (QubitD n) (fun i => qbit (x i))
          (fun _ => norm_qbit _)).embFrame (emb := ctrlEmb n) R hR) (fun _ => True)) := by
  refine .seq (.conseq ?_ (revCircBack_deriv n x R hR) ?_)
    (.conseq (SourceAssertion.entails_refl _) (iqftIter_deriv n x R hR) ?_)
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [framedFam, Assn.embFrame_op, Assn.ofStateFam_op, prodA_op,
        iqftRevFamN_zero]
      exact le_rfl
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [framedFam, Assn.embFrame_op, Assn.ofStateFam_op,
        iqftRevFamN_half, qftStageFam_full]
      exact le_rfl
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      simp only [framedFam, Assn.embFrame_op, prodA_op, Assn.ofStateFam_op, qftStageFam_zero]
      exact le_rfl
end Literal

end Qhl.InverseQFTPlacedSource

namespace Qhl.QPESource
open Finset QPETriple
open scoped ComplexInnerProductSpace ComplexOrder
variable (n : ℕ) [NeZero n] (x : Fin n → Bool) (U : UnitaryOp 𝕢)
variable (ψ : 𝕢) (hψ : ‖ψ‖ = 1)
variable (hU : (U : 𝕢 →ₗ[ℂ] 𝕢) ψ =
  Complex.exp (((2 * Real.pi * ((natVal x : ℝ) / 2 ^ n) : ℝ) : ℂ) * Complex.I) • ψ)

/-- The generic source parallel-Hadamard theorem at the control register. -/
theorem phDeriv :
    SourceDerivTot (σT := ℕ)
      (SourceAssertion.ofAssn
        (prodA (QubitD (n + 1)) (qpeInitFam n ψ) (norm_qpeInitFam n ψ hψ))
        (fun _ => True))
      (phCtrl n)
      (SourceAssertion.ofAssn
        (prodA (QubitD (n + 1)) (qpePlusFam n ψ) (norm_qpePlusFam n ψ hψ))
        (fun σ => σ = n)) := by
  have h0 : qpeInitFam n ψ
      = ParallelHadamardTriple.phFamOn n (ctrlReg n) (fun _ => ψ) 0 := by
    rw [ParallelHadamardTriple.phFamOn_zero]
    funext i
    by_cases h : (i : ℕ) < n
    · rw [if_pos (mem_sig_ctrlReg.mpr h)]
      simp only [qpeInitFam]
      rw [if_pos h]
    · rw [if_neg fun hc => h (mem_sig_ctrlReg.mp hc)]
      simp only [qpeInitFam]
      rw [if_neg h]
  have h1 : ParallelHadamardTriple.phFamOn n (ctrlReg n) (fun _ => ψ) n
      = qpePlusFam n ψ := by
    rw [ParallelHadamardTriple.phFamOn_full]
    funext i
    by_cases h : (i : ℕ) < n
    · rw [if_pos (mem_sig_ctrlReg.mpr h)]
      simp only [qpePlusFam]
      rw [if_pos h]
    · rw [if_neg fun hc => h (mem_sig_ctrlReg.mp hc)]
      simp only [qpePlusFam]
      rw [if_neg h]
  refine SourceDerivTot.conseq ?_
    (ParallelHadamardSource.phDerivOn n (ctrlReg n) CounterLens.nat
      (fun _ => ψ) (fun _ => hψ)) ?_
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _; exact prodA_le h0 σ
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      apply le_of_eq
      rw [prodA_op, prodA_op, h1]

include hU in
/-- Each controlled gate discharges its kickback identity under the loop guard. -/
theorem kickDeriv : SourceDerivTot (σT := ℕ)
    (SourceAssertion.ofAssn
      (prodA (QubitD (n + 1)) (qpePlusFam n ψ) (norm_qpePlusFam n ψ hψ))
      (fun _ => True))
    (kickCir n U)
    (SourceAssertion.ofAssn
      (prodA (QubitD (n + 1)) (qpePhasedFam n x ψ) (norm_qpePhasedFam n x ψ hψ))
      (fun σ => σ = n)) := by
  refine SourceDerivTot.conseq (SourceAssertion.entails_refl _)
    (SourceDerivTot.countedStateChain CounterLens.nat (fun _ => n) (fun _ => True)
      (hv₀ := fun _ => norm_prodV_eq_one _ (norm_qpePlusFam n ψ hψ))
      (hv₁ := fun _ => norm_prodV_eq_one _ (norm_qpePhasedFam n x ψ hψ))
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
      (fun k _ => prodV (QubitD (n + 1)) (W := univ) (qpeKickFam n x ψ k))
      (fun k _ => norm_prodV_eq_one _ (norm_qpeKickFam n x ψ hψ k))
      (fun _ _ _ => rfl)
      (fun _ _ => congrArg _ (qpeKickFam_zero n x ψ))
      (fun _ _ => congrArg _ (qpeKickFam_full n x ψ)) ?_ ?_) ?_
  · exact SourceDerivTot.countedRung_pair_fam (kickRegE n) (kickGate n U)
      (qpeCell n) (fun _ => Fin.last n) (fun σ _ => qpeCell_ne_last n σ)
      (fun σ => control (U ^ 2 ^ (n - 1 - σ)))
      (fun σ => norm_qpeKickFam n x ψ hψ σ)
      (fun σ => norm_qpeKickFam n x ψ hψ (σ + 1))
      (fun σ _ => ⟨(Reg.pair _ _ (qpeCell_ne_last n σ)).inj, rfl⟩)
      (fun σ hσ => by
        have hk : σ < n := hσ.2
        refine ⟨phaseKet (qftAngle x (n - 1 - σ)), ψ, ?_, ?_⟩
        · have hctrl : qpeKickFam n x ψ σ (qpeCell n σ) = qplus := by
            rw [qpeCell_of_lt n hk]
            exact qpeKickFam_ctrl n x ψ ⟨σ, hk⟩
          rw [hctrl, qpeKickFam_last n x ψ σ, ← phaseKet_zero,
            control_pow_vpair_phaseKet U hU (2 ^ (n - 1 - σ)) 0, zero_add,
            phaseKet_kick n x (show n - 1 - σ < n by omega)]
        · rw [qpeCell_of_lt n hk]
          exact qpeKickFam_step n x ψ ⟨σ, hk⟩)
  · intro z
    exact SourceDerivTot.unitary_identity (kickRegE n) (kickGate n U) _
      (fun σ _ => (Reg.pair _ _ (qpeCell_ne_last n σ)).inj)
  · apply SourceAssertion.entails_ofAssn
    · intro σ h; exact h.2
    · intro σ _; exact le_rfl
/-- The untouched target-qubit factor used to instantiate the placed inverse circuit. -/
noncomputable def targetFrame :=
  prodV (QubitD (n + 1)) (W := univ \ embRange (ctrlEmb n)) (qpeInitFam n ψ)

include hψ in
theorem norm_targetFrame : ‖targetFrame n ψ‖ = 1 :=
  norm_prodV_eq_one _ (norm_qpeInitFam n ψ hψ)

private theorem outside_target (i : Fin (n + 1)) (hi : i ∈ univ \ embRange (ctrlEmb n)) :
    i = Fin.last n := by
  have hns : ¬ (i : ℕ) < n := by
    intro hc
    exact (mem_sdiff.mp hi).2 (mem_map.mpr
      ⟨⟨i.val, hc⟩, mem_univ _, Fin.ext rfl⟩)
  exact Fin.ext (by have := i.isLt; simp; omega)

/-- Mathematical product-frame identity; it contains no program derivation. -/
private theorem frame_endpoint
    (f : Fin (n + 1) → 𝕢) (hf : ∀ i, ‖f i‖ = 1) (hout : f (Fin.last n) = ψ) :
    (prodA (σT := ℕ) (QubitD n) (fun j => f j.castSucc) (fun j => hf j.castSucc)).embFrame
      (emb := ctrlEmb n) (outerLM (targetFrame n ψ) (targetFrame n ψ))
      (isEffect_outerLM_self (norm_targetFrame n ψ hψ)) =
      prodA (QubitD (n + 1)) f hf := by
  have he : targetFrame n ψ =
      prodV (QubitD (n + 1)) (W := univ \ embRange (ctrlEmb n)) f := by
    apply prodV_congr
    intro i hi
    rw [outside_target n i hi, hout]
    simp [qpeInitFam]
  simp only [he]
  exact Assn.embFrame_prodA (ctrlEmb n) f hf

/-- The placed inverse-QFT source proof with the target eigenstate as its frame. -/
theorem iqftCtrlDeriv : SourceDerivTot (σT := ℕ)
    (SourceAssertion.ofAssn
      (prodA (QubitD (n + 1)) (qpePhasedFam n x ψ) (norm_qpePhasedFam n x ψ hψ))
      (fun _ => True))
    (iqftCtrl n)
    (SourceAssertion.ofAssn
      (prodA (QubitD (n + 1)) (qpeOutFam n x ψ) (norm_qpeOutFam n x ψ hψ))
      (fun _ => True)) := by
  have hin := frame_endpoint n ψ hψ (qpePhasedFam n x ψ)
    (norm_qpePhasedFam n x ψ hψ) (qpePhasedFam_last n x ψ)
  have hout := frame_endpoint n ψ hψ (qpeOutFam n x ψ)
    (norm_qpeOutFam n x ψ hψ) (qpeOutFam_last n x ψ)
  simp only [qpePhasedFam_castSucc] at hin
  simp only [qpeOutFam_castSucc] at hout
  have hd := InverseQFTPlacedSource.Literal.iqftProdDeriv n x
    (outerLM (targetFrame n ψ) (targetFrame n ψ))
    (isEffect_outerLM_self (norm_targetFrame n ψ hψ))
  rw [hin, hout] at hd
  exact hd

include hU in
/-- The exact original QPE triple, using source proofs for all three stages. -/
theorem qpeDeriv : SourceDerivTot (σT := ℕ)
    (SourceAssertion.ofAssn
      (prodA (QubitD (n + 1)) (qpeInitFam n ψ) (norm_qpeInitFam n ψ hψ))
      (fun _ => True))
    (qpeCir n U)
    (SourceAssertion.ofAssn
      (prodA (QubitD (n + 1)) (qpeOutFam n x ψ) (norm_qpeOutFam n x ψ hψ))
      (fun _ => True)) := by
  refine (phDeriv n ψ hψ).seq ((SourceDerivTot.conseq ?_
    (kickDeriv n x U ψ hψ hU) (SourceAssertion.entails_refl _)).seq
      (SourceDerivTot.conseq ?_ (iqftCtrlDeriv n x ψ hψ)
        (SourceAssertion.entails_refl _)))
  · apply SourceAssertion.entails_ofAssn
    · intro _ _; trivial
    · intro _ _; exact le_rfl
  · apply SourceAssertion.entails_ofAssn
    · intro _ _; trivial
    · intro _ _; exact le_rfl

include hU in
/-- Source soundness recovers the exact original semantic specification. -/
theorem qpeValid : validTot (σT := ℕ)
    (prodA (QubitD (n + 1)) (qpeInitFam n ψ) (norm_qpeInitFam n ψ hψ))
    (qpeCir n U)
    (prodA (QubitD (n + 1)) (qpeOutFam n x ψ) (norm_qpeOutFam n x ψ hψ)) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (qpeDeriv n x U ψ hψ hU).sound
end Qhl.QPESource
