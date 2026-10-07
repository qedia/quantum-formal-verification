import Qhl.Logic.Source.CountedStateChain
import Qhl.Logic.ProductStateFam
import Qhl.Logic.CountedProdChain
import Qhl.Logic.CountedStateChain
import Qhl.Logic.Soundness
import Qhl.Register.GraphState

/-! # The 1D cluster-state preparation triple

Cluster (graph) state preparation — Briegel–Raussendorf 2001 — on the standard
`n`-qubit world: a Hadamard on every wire, then the Ising-type entangling layer
of `CZ` gates on the `n - 1` nearest-neighbour pairs, and its triple in
`QHL⁺_tot`:

```
⊢ₜ { ∣0…0⟩ }  hLayer ;; czChain  { ∣C_n⟩ },

C_n = 2^{-n/2} ∑_y (-1)^{∑_{j<n-1} y_j·y_{j+1}} ∣y⟩.
```

**Both loops are genuine `while` loops.** The printed system of the QHL⁺ paper
has no rule for any other loop shape, so each layer is the counted loop
`cnt := 0 ; while cnt < N do BODY ; cnt := cnt + 1 od` (`countedProg`) over the
store `σT = ℕ` (`CounterLens.nat`, the one counter re-initialised by each
loop), discharged by **one packaged-rule call per loop** — each rule derived
from the printed constructors only: (Ax-Ass), (Ax-Uni), (R-Seq), (R-Cond),
(R-Conseq), and **(R-Loop-tot)** with the integer variant `t σ = N − cnt σ`:

* the **Hadamard layer** by ONE `DerivTot.countedProdChainSource`
  (`Qhl/Logic/CountedProdChain.lean`) along the library product-state
  staircase family `hadFam` (`Qhl/Register/Qubits.lean`: first `k` cells
  `∣+⟩`, the rest `∣0⟩`); each pass is one one-cell
  rung `DerivTot.countedRung_single` at the gate fact `H_q0`;
* the **CZ chain** by ONE `DerivTot.countedStateChainSource`
  (`Qhl/Logic/CountedStateChain.lean`) along the library family
  `clusterFam n k` (`Qhl/Register/GraphState.lean`) — the state after `k`
  edges. The passes **share wires** (edge `k` and edge `k+1` meet at cell
  `k+1`) and the mid-loop states are **entangled**, not products, so the chain
  runs at store-indexed pure-state endpoints (`Assn.ofStateFam`), each pass one
  rung `DerivTot.countedRung_fam` at the library edge fact `clusterFam_step`;
  `clusterFam` is `ℕ`-indexed already (`edgeSign` is total in the edge index),
  so no re-indexing is needed, and it is store-constant, so the
  counter-insensitivity premise is `rfl`;
* the two glued by (R-Seq), the loop-entry identification
  `clusterFam n 0 = ⊗ᵢ ∣+⟩` by `clusterFam_zero`, the counter masks collapsed
  by (R-Conseq) at the endpoints — both endpoints are store-constant, so the
  triple holds at an arbitrary initial counter value.

The registers are genuine store-dependent register expressions (`RegExpr`, the
paper's `q̄(t̄)`), reading the touched cell `cell n k` off the counter
(`Qhl/Register/Qubits.lean`); `[NeZero n]` is forced by their totality, and
where the pair expression degenerates (off the loop mask, `n = 1` only) the
bundled gate is `1` — the paper's `Dist(q̄)` side condition is discharged only
where the masks hold, exactly as in `Qhl/Examples/QFTTriple.lean`.

The triple is genuine and non-vacuous: the precondition is literally the
computational basis ket `∣0…0⟩` (`preState_eq_deltav`), the postcondition the
distinct unit vector `∣C_n⟩` — pinned to its signed basis-sum form by
`clusterState_eq_sum`, with nonzero `∣0…0⟩` coordinate `2^{-n/2}`
(`clusterVec_apply_allFalse`). Both assertions are projector effects on
density operators, and `clusterValid` runs `clusterDeriv` through soundness.

Beyond the coordinate formula, §6 records the **stabilizer corollary**
(`clusterState_stabilized`): the verified output `∣C_n⟩` satisfies
`K_j ∣C_n⟩ = ∣C_n⟩` for every standard cluster stabilizer
`K_j = Z_{j-1} X_j Z_{j+1}` (`clusterStab_clusterVec`,
`Qhl/Register/GraphState.lean`) — the abstract graph-state specification. -/

namespace Qhl.ClusterStateTriple

open Finset

section

variable (n : ℕ) [NeZero n]

/-! ## §1. The registers and gates, as store-dependent expressions -/

/-- The one-cell register expression `q[cnt]` of the Hadamard layer. -/
def hReg : RegExpr ℕ (QubitL n) 1 := fun σ => (Reg.single (cell n σ)).toFun

/-- The Hadamard on the tuple space of the one-cell register. -/
noncomputable def hGate (σ : ℕ) : UnitaryOp (TSpace (QubitD n) (hReg n σ)) :=
  singleGate (QubitD n) (cell n σ) H

/-- The two-cell register expression `(q[cnt], q[cnt+1])` of an entangling
edge. -/
def czReg : RegExpr ℕ (QubitL n) 2 := fun σ => ![cell n σ, cell n (σ + 1)]

/-- The `CZ` on the tuple space of the edge's register; `1` where the register
expression degenerates (off the loop mask, `n = 1` only). -/
noncomputable def czGate (σ : ℕ) : UnitaryOp (TSpace (QubitD n) (czReg n σ)) :=
  if h : cell n σ ≠ cell n (σ + 1) then
    pairGate (cell n σ) (cell n (σ + 1)) h CZ
  else 1

/-! ## §2. The program: two counted `while` loops

Program constructors `.assign`, `.while`, `.seq`, `.unitary` only; the single
counter of the store `σT = ℕ` is re-initialised by each loop. -/

/-- **The Hadamard layer**: the counted loop
`cnt := 0 ; while cnt < n do q[cnt] *= H ; cnt := cnt + 1 od`. -/
noncomputable def hLayer : Prog ℕ (QubitD n) :=
  countedProg CounterLens.nat (fun _ => n) (.unitary 1 (hReg n) (hGate n))

/-- **The entangling layer**: the counted loop
`cnt := 0 ; while cnt < n−1 do (q[cnt], q[cnt+1]) *= CZ ; cnt := cnt + 1 od`
over the `n − 1` nearest-neighbour edges. -/
noncomputable def czChain : Prog ℕ (QubitD n) :=
  countedProg CounterLens.nat (fun _ => n - 1) (.unitary 2 (czReg n) (czGate n))

/-- **The program** (E-1): the Hadamard layer, then the `CZ` chain. -/
noncomputable def clusterProg : Prog ℕ (QubitD n) := (hLayer n).seq (czChain n)

/-! ## §3. The Hadamard layer: one counted product-state chain

The loop-invariant family is the library staircase `hadFam`
(`Qhl/Register/Qubits.lean`, Layer 4): after `k` passes the first `k` cells
are `∣+⟩`, the rest still `∣0⟩`. -/

/-- The Hadamard layer, `⊗ᵢ ∣0⟩ → ⊗ᵢ ∣+⟩`: ONE `DerivTot.countedProdChainSource`
along `hadFam`; each pass one `DerivTot.countedRung_single` at `H_q0`. -/
theorem hadamardDeriv :
    DerivTot (σT := ℕ)
      (prodA (QubitD n) (fun _ => q0) fun _ => norm_q0)
      (hLayer n)
      ((prodA (QubitD n) (fun _ => qplus) fun _ => norm_qplus).mask
        fun σ => σ = n) :=
  DerivTot.countedProdChainSource CounterLens.nat
    (hadFam n) (norm_hadFam n) (hadFam_zero n) (hadFam_full n)
    (DerivTot.countedRung_single_fam (hReg n) (hGate n) (cell n) (fun _ => H)
      (fun σ => norm_hadFam n σ) (fun σ => norm_hadFam n (σ + 1))
      (fun σ _ => ⟨(Reg.single (cell n σ)).inj, rfl⟩)
      (fun σ hσ => by
        change σ < n at hσ
        rw [hadFam_ctrl n hσ, H_q0]
        exact hadFam_step n hσ))
    (fun _ => DerivTot.unitary_identity_mask (hReg n) (hGate n)
      (fun σ _ => (Reg.single (cell n σ)).inj))

/-! ## §4. The CZ chain: one counted state-family chain -/

/-- The entangling layer, `⊗ᵢ ∣+⟩ → ∣C_n⟩`: ONE `DerivTot.countedStateChainSource`
along the library family `clusterFam` — entangled mid-loop, hence
state-family, not product, endpoints; each pass one `DerivTot.countedRung_fam`
at the library edge fact `clusterFam_step` (through the cell-indexed library
bridge `clusterFam_step_cell`).
The family is store-constant, so counter insensitivity is `rfl`. -/
theorem czChainDeriv :
    DerivTot (σT := ℕ)
      (Assn.ofStateFam (fun _ => allPlus n) fun _ => norm_allPlus n)
      (czChain n)
      ((Assn.ofStateFam (fun _ => clusterVec n) fun _ => norm_clusterVec n).mask
        fun σ => σ = n - 1) :=
  DerivTot.countedStateChainSource CounterLens.nat
    (fun k _ => clusterFam n k) (fun k _ => norm_clusterFam n k)
    (fun _ _ _ => rfl)
    (funext fun _ => clusterFam_zero n) rfl
    (DerivTot.countedRung_fam (czReg n) (czGate n)
      (fun σ => norm_clusterFam n σ) (fun σ => norm_clusterFam n (σ + 1))
      (fun σ hσ => by
        change σ < n - 1 at hσ
        have hlt : σ + 1 < n := by omega
        have hne : cell n σ ≠ cell n (σ + 1) :=
          cell_ne n (Nat.lt_of_succ_lt hlt) hlt (Nat.ne_of_lt (Nat.lt_succ_self σ))
        refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
        rw [show czGate n σ = pairGate (cell n σ) (cell n (σ + 1)) hne CZ from by
          simp only [czGate]; rw [dif_pos hne]]
        exact clusterFam_step_cell hlt
          (cell_eq_mk n (Nat.lt_of_succ_lt hlt)) (cell_eq_mk n hlt) hne))
    (fun k => DerivTot.unitary_identity_mask (czReg n) (czGate n) (fun σ hσ => by
      have hlt : σ + 1 < n := by
        change σ = k ∧ k < n - 1 at hσ
        omega
      exact (Reg.pair _ _ (cell_ne n (by omega) hlt (by omega))).inj))

/-! ## §5. The triple and its soundness -/

/-- **The cluster-state preparation triple** (E-2/E-3):

```
⊢ₜ { ∣0…0⟩⟨0…0∣ }  clusterProg n  { ∣C_n⟩⟨C_n∣ }
```

— (R-Seq) of the two loop derivations, (R-Conseq) collapsing the counter masks
at the store-constant endpoints; every program constructor matched to its
rule. -/
theorem clusterDeriv :
    DerivTot (σT := ℕ) (D := QubitD n)
      (allZerosA (QubitL n) ℕ)
      (clusterProg n)
      (Assn.ofState (clusterVec n) (norm_clusterVec n)) :=
  DerivTot.seq
    (DerivTot.conseq (Assn.ofState_le_ofState rfl) (hadamardDeriv n)
      (Assn.le_refl' _))
    (DerivTot.conseq
      (Assn.mask_le_of_imp_le fun σ _ => le_of_eq (by
        rw [prodA_op, Assn.ofStateFam_op]; rfl))
      (czChainDeriv n)
      (Assn.mask_le_of_imp_le fun σ _ => le_of_eq (by
        rw [Assn.ofStateFam_op, Assn.ofState_op])))

/-- **The triple, semantically** (E-4) — `clusterDeriv` through soundness: for
**every** input density operator and every initial counter value, the
expectation of `∣0…0⟩⟨0…0∣` bounds the terminal expectation of
`∣C_n⟩⟨C_n∣`. -/
theorem clusterValid :
    validTot (σT := ℕ) (D := QubitD n)
      (allZerosA (QubitL n) ℕ)
      (clusterProg n)
      (Assn.ofState (clusterVec n) (norm_clusterVec n)) :=
  (clusterDeriv n).sound

end

/-! ## §6. Non-vacuity: both endpoints pinned -/

variable (n : ℕ)

/-- The precondition is literally the computational basis ket `∣0…0⟩`. -/
theorem preState_eq_deltav :
    allZerosOn (QubitL n) = deltav (QubitD n) fun _ => false :=
  allZerosOn_eq_deltav (QubitL n)

/-- The postcondition is literally the signed basis sum
`2^{-n/2} ∑_y (-1)^{∑_{j<n-1} y_j·y_{j+1}} ∣y⟩` — the 1D cluster state. -/
theorem clusterState_eq_sum :
    clusterVec n
      = ∑ m : Fin n → Bool,
          (((Real.sqrt 2 : ℂ))⁻¹ ^ n * czSign n (n - 1) m)
            • deltav (QubitD n) (fun i : ↥(univ : Finset (QubitL n)) => m (i : QubitL n)) :=
  clusterFam_eq_sum n (n - 1)

/-- The postcondition is a nonzero predicate: `∣C_n⟩ ≠ 0` (its `∣0…0⟩`
coordinate is `2^{-n/2}`, `clusterVec_apply_allFalse`). -/
theorem clusterState_ne_zero : clusterVec n ≠ 0 := clusterVec_ne_zero n

/-- **Stabilizer corollary**: the verified postcondition state `∣C_n⟩` is a
`+1`-eigenvector of every standard cluster stabilizer

```
K_j = Z_{j-1} X_j Z_{j+1}     (j = 0, …, n-1;  K_0 = X_0 Z_1,  K_{n-1} = Z_{n-2} X_{n-1})
```

(`clusterStab`, `Qhl/Register/GraphState.lean`) — so the output of the
verified program meets the abstract graph-state specification of the cluster
state, not only the coordinate formula `clusterState_eq_sum`.  What is proved
here are the `n` eigenvalue equations; that the `n` stabilizers determine
`∣C_n⟩` uniquely up to phase is the standard stabilizer-formalism fact and is
not formalized. -/
theorem clusterState_stabilized (j : Fin n) :
    clusterStab n j (clusterVec n) = clusterVec n :=
  clusterStab_clusterVec n j

end Qhl.ClusterStateTriple

#print axioms Qhl.ClusterStateTriple.clusterDeriv
#print axioms Qhl.ClusterStateTriple.clusterValid
#print axioms Qhl.ClusterStateTriple.clusterState_stabilized

/-! # Cluster preparation through source counted loops -/
namespace Qhl.ClusterStateTriple
open Finset
variable (n : ℕ) [NeZero n]

/-- The Hadamard loop retains its exact exit counter as a classical condition. -/
theorem hadamardSourceDeriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (allZerosA (QubitL n) ℕ) (fun _ => True))
      (hLayer n)
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun _ : ℕ => allPlus n) (fun _ => norm_allPlus n))
        (fun σ => True ∧ σ = n)) := by
  apply SourceDerivTot.countedStateChain CounterLens.nat (fun _ => n) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k _ => prodV (QubitD n) (hadFam n k))
    (fun k _ => norm_prodV_eq_one _ (norm_hadFam n k))
    (hv₀ := fun _ => norm_allZerosOn (QubitL n))
    (fun _ _ _ => rfl)
  · intro σ _
    rw [hadFam_zero]
    rfl
  · intro σ _
    rw [hadFam_full]
    rfl
  · apply SourceDerivTot.unitary_stateFam_guard (hReg n) (hGate n)
      _ _ _ _ _ (fun σ _ => (Reg.single (cell n σ)).inj)
    intro σ hσ
    change regLift (Reg.single (cell n σ))
      (singleGate (QubitD n) (cell n σ) H) (prodV (QubitD n) (hadFam n σ)) = _
    change True ∧ σ < n at hσ
    change _ = prodV (QubitD n) (hadFam n (σ + 1))
    rw [regLift_singleGate_prodV, hadFam_ctrl n hσ.2, H_q0, hadFam_step n hσ.2]
  · intro z
    exact SourceDerivTot.unitary_identity _ _ _ (fun σ _ => (Reg.single (cell n σ)).inj)

/-- The CZ loop retains its exact exit counter and uses the entangled state family. -/
theorem czChainSourceDeriv :
    SourceDerivTot
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun _ : ℕ => allPlus n) (fun _ => norm_allPlus n))
        (fun _ => True))
      (czChain n)
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun _ : ℕ => clusterVec n) (fun _ => norm_clusterVec n))
        (fun σ => True ∧ σ = n - 1)) := by
  have hd (σ : ℕ) (h : σ < n - 1) : Function.Injective (czReg n σ) := by
    have hlt : σ + 1 < n := by omega
    exact (Reg.pair _ _ (cell_ne n (by omega) hlt (by omega))).inj
  apply SourceDerivTot.countedStateChain CounterLens.nat (fun _ => n - 1) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k _ => clusterFam n k) (fun k _ => norm_clusterFam n k)
    (fun _ _ _ => rfl) (fun _ _ => clusterFam_zero n) (fun _ _ => rfl)
  · apply SourceDerivTot.unitary_stateFam_guard (czReg n) (czGate n)
      _ _ _ _ _ (fun σ h => hd σ h.2)
    intro σ hσ
    have hlt : σ + 1 < n := by have := hσ.2; change σ < n - 1 at this; omega
    have hne : cell n σ ≠ cell n (σ + 1) :=
      cell_ne n (by omega) hlt (by omega)
    rw [show czGate n σ = pairGate (cell n σ) (cell n (σ + 1)) hne CZ from by
      simp only [czGate]; rw [dif_pos hne]]
    exact clusterFam_step_cell hlt (cell_eq_mk n (by omega)) (cell_eq_mk n hlt) hne
  · intro z
    exact SourceDerivTot.unitary_identity _ _ _ (fun σ h => hd σ h.2.1)

/-- The exact original cluster program and quantum endpoints through source rules. -/
theorem clusterSourceDeriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (allZerosA (QubitL n) ℕ) (fun _ => True))
      (clusterProg n)
      (SourceAssertion.ofAssn (Assn.ofState (clusterVec n) (norm_clusterVec n))
        (fun _ => True)) := by
  refine .seq (hadamardSourceDeriv n) (.conseq ?_ (czChainSourceDeriv n) ?_)
  · apply SourceAssertion.entails_ofAssn
    · intro _ _; trivial
    · intro _ _; exact le_rfl
  · apply SourceAssertion.entails_ofAssn
    · intro _ _; trivial
    · intro _ _; exact le_rfl

/-- The original cluster semantic triple, obtained from source soundness. -/
theorem clusterSourceValid :
    validTot (allZerosA (QubitL n) ℕ) (clusterProg n)
      (Assn.ofState (clusterVec n) (norm_clusterVec n)) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (clusterSourceDeriv n).sound

end Qhl.ClusterStateTriple

#print axioms Qhl.ClusterStateTriple.clusterSourceDeriv
#print axioms Qhl.ClusterStateTriple.clusterSourceValid
