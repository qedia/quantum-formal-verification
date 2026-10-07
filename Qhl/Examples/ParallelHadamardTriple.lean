import Qhl.Logic.Source.CountedWhile
import Qhl.Logic.ProductStateFam
import Qhl.Logic.Soundness
import Qhl.Logic.CountedProdChain
import Qhl.Gate.Qubit
import Qhl.HSpace.LocalGate
import Qhl.Register.Qubits

/-!
# E-4 / L-7f: the parallel Hadamard, as a total-correctness triple

CoqQ's `RS_ParaHadamard_tuple0` (`example.v`): the program that hits every cell
of an `n`-qubit world with a Hadamard,

```
{⊗ᵢ ∣0⟩}  for i do  ut x[i] := H  {⊗ᵢ ∣+⟩}
```

CoqQ's `for` loop is rendered here as the counted `while` loop

```
i := 0;  while i < n do  x[i] *= H;  i := i + 1  od
```

over the classical state space `σT = ℕ` (the loop counter), and the triple is
derived in `QHL⁺_tot` with the source **(R-Loop-tot)** —
`DerivTot.whileLoopSource` — with the
interpolating product state

```
∣φ_σ⟩ = ∣+⟩^{⊗σ} ⊗ ∣0⟩^{⊗(n-σ)}   (`plusAt σ`)
```

as loop invariant (`J`) and the ranking function `t σ = n - σ`. The single
piece of state algebra is `K_plusAt`: one Hadamard on the cell `σ` turns
`∣φ_σ⟩` into `∣φ_{σ+1}⟩` — and that is now one application of the library
one-site bridge `gateAt_prodV` (`Qhl/Register/Qubits.lean`), the interpolant
itself being the library product state `prodV`. Everything else is the proof
system: two axioms (Ax-Uni, Ax-Ass), (R-Seq), (R-Conseq) and the loop rule —
the triple is never unfolded by induction on the program.

The **fixture** — the standard `n`-qubit world `QubitL n`/`QubitD n`, the
endpoint states `allZeros n = ⊗ᵢ ∣0⟩` and `allPlus n = ⊗ᵢ ∣+⟩` with their
norms and coordinates (`allPlus_apply`: every coordinate is `2^{-n/2}`), their
assertion forms, and the one-site gate `gateAt a U` with its unitarity and its
action on a product state — is the library module `Qhl/Register/Qubits.lean`.
What is genuinely this example's own content is the interpolant `plusAt` and
the loop derivation, glued to the library endpoints by `plusAt_zero`
(`plusAt 0 = ⊗ᵢ ∣0⟩`) and `plusAt_top` (`plusAt n = ⊗ᵢ ∣+⟩`) — the literal
CoqQ endpoints.
-/

namespace Qhl.ParallelHadamardTriple

open Qhl Finset
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal

section

variable (n : ℕ) [NeZero n]

/-! ## §1. The fixture: `n` qubit cells, the counter as classical state -/

/-- The register expression `x[i]` of the loop body (W3): the one-cell
register naming the cell `i`. -/
def regE : RegExpr ℕ (QubitL n) 1 := fun σ => (Reg.single (cell n σ)).toFun

/-- The paper's `Dist(q̄)` (eq (2)) is free for a one-cell register. -/
theorem distE (σ : ℕ) : Function.Injective (regE n σ) := (Reg.single (cell n σ)).inj

/-- The library Hadamard on the tuple space of the one-cell register (R-2). -/
noncomputable def gate (σ : ℕ) : UnitaryOp (TSpace (QubitD n) (regE n σ)) :=
  singleGate (QubitD n) (cell n σ) H

/-- `H` on the cell `σ`, extended to the whole world (W6): the library one-site
gate `gateAt`. -/
noncomputable def K (σ : ℕ) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  gateAt (QubitL n) (cell n σ) H

theorem regLift_regE (σ : ℕ) : regLift ⟨regE n σ, distE n σ⟩ (gate n σ) = K n σ := rfl

theorem isUnitary_K (σ : ℕ) : IsUnitary (K n σ) := isUnitary_gateAt (QubitL n) (cell n σ) H

/-- The loop guard `i < n`. -/
def bGuard (σ : ℕ) : Bool := decide (σ < n)

/-- The loop body `x[i] *= H; i := i + 1`. -/
noncomputable def body : Prog ℕ (QubitD n) :=
  (Prog.unitary 1 (regE n) (gate n)).seq (Prog.assign fun σ => σ + 1)

/-- E-4: the program `i := 0; while i < n do x[i] *= H; i := i + 1 od`. -/
noncomputable def phProg : Prog ℕ (QubitD n) :=
  (Prog.assign fun _ => 0).seq (Prog.while (bGuard n) (body n))

/-! ## §2. The interpolating product state `∣+⟩^{⊗σ} ⊗ ∣0⟩^{⊗(n-σ)}` -/

/-- The `j`-th factor of the interpolating state: already Hadamarded below
`σ`, still `∣0⟩` from `σ` on. -/
noncomputable def cellVec (σ : ℕ) (j : Fin n) : 𝕢 := if (j : ℕ) < σ then qplus else q0

/-- The interpolating product state `∣+⟩^{⊗σ} ⊗ ∣0⟩^{⊗(n-σ)}`: the library
per-cell product state (`prodV`) of those factors. -/
noncomputable def plusAt (σ : ℕ) : HS (QubitD n) (univ : Finset (QubitL n)) :=
  prodV (QubitD n) (cellVec n σ)

omit [NeZero n] in
/-- At `σ = 0` the interpolating state is the library `⊗ᵢ ∣0⟩`: every factor is
still `∣0⟩`. -/
theorem plusAt_zero : plusAt n 0 = allZeros n := by
  rw [plusAt, allZeros, allZerosOn]
  exact prodV_congr (QubitD n) fun j _ => by simp [cellVec]

omit [NeZero n] in
/-- At `σ = n` the interpolating state is the library `⊗ᵢ ∣+⟩`: every factor
has been Hadamarded. -/
theorem plusAt_top : plusAt n n = allPlus n := by
  rw [plusAt, allPlus, allPlusOn]
  exact prodV_congr (QubitD n) fun j _ => by simp only [cellVec, if_pos j.isLt]

omit [NeZero n] in
/-- Beyond `σ = n` nothing moves: every factor is already `∣+⟩`. -/
theorem plusAt_of_ge {σ : ℕ} (h : n ≤ σ) : plusAt n σ = plusAt n n :=
  prodV_congr (QubitD n) fun j _ => by
    simp only [cellVec, if_pos (lt_of_lt_of_le j.isLt h), if_pos j.isLt]

/-- The interpolating states are unit vectors: every factor is (library
`norm_prodV`). -/
theorem norm_plusAt (σ : ℕ) : ‖plusAt n σ‖ = 1 := by
  rw [plusAt, norm_prodV (QubitD n) (W := (univ : Finset (QubitL n))) (cellVec n σ)]
  refine Finset.prod_eq_one fun i _ => ?_
  simp only [cellVec]
  split <;> simp

/-! ## §3. The one real computation: one Hadamard advances the interpolant -/

/-- **The computation**: the Hadamard on the cell `σ` advances the
interpolating state one step, `∣φ_σ⟩ ↦ ∣φ_{σ+1}⟩`. This is the library one-site
bridge `gateAt_prodV` (CoqQ `tentf_tuple_apply` under `lift_lf`) plus the
one-line check that updating the `σ`-th factor of `cellVec σ` gives
`cellVec (σ+1)`. -/
theorem K_plusAt {σ : ℕ} (hσ : σ < n) : K n σ (plusAt n σ) = plusAt n (σ + 1) := by
  have hb := gateAt_prodV (QubitL n) (cell n σ) H (cellVec n σ)
  refine hb.trans (prodV_congr (QubitD n) fun j _ => ?_)
  rcases eq_or_ne j (cell n σ) with rfl | hj
  · have h0 : cellVec n σ (cell n σ) = q0 := by simp [cellVec, cell_val n hσ]
    rw [Function.update_self, h0, H_q0]
    simp [cellVec, cell_val n hσ]
  · have hne : (j : ℕ) ≠ σ := fun hv => hj (Fin.ext (hv.trans (cell_val n hσ).symm))
    rw [Function.update_of_ne hj]
    simp only [cellVec,
      show ((j : ℕ) < σ + 1) = ((j : ℕ) < σ) by simp only [eq_iff_iff]; omega]

/-! ## §4. The assertions, the loop invariant, and the derivation -/

/-- The loop invariant: "the world is in the interpolating state `∣φ_i⟩`". -/
noncomputable def J : Assn ℕ (QubitD n) :=
  ⟨fun σ => outerLM (plusAt n σ) (plusAt n σ), fun σ => isEffect_outerLM_self (norm_plusAt n σ)⟩

@[simp] theorem J_op (σ : ℕ) : (J n).op σ = outerLM (plusAt n σ) (plusAt n σ) := rfl

/-- The precondition "the world is in `⊗ᵢ ∣0⟩`" — the library assertion. -/
noncomputable def P0 : Assn ℕ (QubitD n) := allZerosA (QubitL n) ℕ

omit [NeZero n] in
@[simp] theorem P0_op (σ : ℕ) : (P0 n).op σ = outerLM (allZeros n) (allZeros n) := rfl

/-- The postcondition "the world is in `⊗ᵢ ∣+⟩`" — the library assertion. -/
noncomputable def Pplus : Assn ℕ (QubitD n) := allPlusA (QubitL n) ℕ

@[simp] theorem Pplus_op (σ : ℕ) : (Pplus n).op σ = outerLM (allPlus n) (allPlus n) := rfl

/-- The ranking function of (R-Loop-tot): the number of cells still to do. -/
def rank (σ : ℕ) : ℕ := n - σ

/-- The body's premise for the ranking value `m`: (Ax-Uni) and (Ax-Ass), glued
by (R-Seq), with (R-Conseq) discharging the invariant step — and the
entailment it needs is exactly `K_plusAt`. -/
theorem premise_le (m : ℕ) :
    ((J n).mand (bGuard n)).mask (fun σ => rank n σ = m)
      ≤ (((J n).mask fun σ => rank n σ < m).comp fun σ => σ + 1).unitaryPre (regE n) (gate n) := by
  intro σ
  by_cases hm : rank n σ = m
  · by_cases hg : bGuard n σ = true
    · have hσ : σ < n := by simpa [bGuard] using hg
      have hlt : rank n (σ + 1) < m := by simp only [rank] at hm ⊢; omega
      refine le_of_eq ?_
      rw [Assn.mask_op_of_pos (A := (J n).mand (bGuard n))
          (φ := fun σ => rank n σ = m) (σ := σ) hm,
        Assn.mand_op_of_true (A := J n) (b := bGuard n) (σ := σ) hg,
        Assn.unitaryPre_op_of_dist _ (regE n) (gate n) (distE n σ), regLift_regE,
        Assn.comp_op, Assn.mask_op_of_pos (A := J n)
          (φ := fun σ => rank n σ < m) (σ := σ + 1) hlt, J_op, J_op,
        adjoint_comp_outerLM_comp, ← K_plusAt n hσ,
        adjoint_apply_apply (isUnitary_K n σ)]
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := (J n).mand (bGuard n))
        (φ := fun σ => rank n σ = m) (σ := σ) hm]
      exact Assn.mand_op_of_false (A := J n) (b := bGuard n) (σ := σ) (by simpa using hg)
  · exact Assn.op_zero_le (Assn.mask_op_of_neg (A := (J n).mand (bGuard n))
      (φ := fun σ => rank n σ = m) (σ := σ) hm)

theorem bodyDeriv (m : ℕ) :
    DerivTot (((J n).mand (bGuard n)).mask fun σ => rank n σ = m) (body n)
      ((J n).mask fun σ => rank n σ < m) :=
  DerivTot.seq
    (DerivTot.conseq (premise_le n m)
      (DerivTot.unitary (regE n) (gate n) _) (Assn.le_refl' _))
    (DerivTot.assign (fun σ => σ + 1) ((J n).mask fun σ => rank n σ < m))

/-- The source loop rule's separate invariant-preservation premise. -/
theorem bodyInvariantDeriv :
    DerivTot ((J n).mand (bGuard n)) (body n) (J n) := by
  apply DerivTot.seq (B := (J n).comp fun σ => σ + 1) _
    (DerivTot.assign (fun σ => σ + 1) (J n))
  apply DerivTot.conseq _ (DerivTot.unitary (regE n) (gate n) _) (Assn.le_refl' _)
  intro σ
  by_cases hg : bGuard n σ = true
  · have hσ : σ < n := by simpa [bGuard] using hg
    refine le_of_eq ?_
    rw [Assn.mand_op_of_true hg,
      Assn.unitaryPre_op_of_dist _ (regE n) (gate n) (distE n σ), regLift_regE,
      Assn.comp_op, J_op, J_op, adjoint_comp_outerLM_comp,
      ← K_plusAt n hσ, adjoint_apply_apply (isUnitary_K n σ)]
  · exact Assn.op_zero_le (Assn.mand_op_of_false (by simpa using hg))

/-- Identity-predicate decrease is independent of the quantum invariant:
unitarity preserves all mass, and the assignment decreases the counter rank. -/
theorem bodyIdentityRankDeriv (z : ℤ) :
    DerivTot
      ((Assn.one : Assn ℕ (QubitD n)).mask fun σ =>
        True ∧ bGuard n σ = true ∧ (rank n σ : ℤ) = z)
      (body n)
      ((Assn.one : Assn ℕ (QubitD n)).mask fun σ => (rank n σ : ℤ) < z) := by
  let B : Assn ℕ (QubitD n) := Assn.one.mask fun σ => (rank n σ : ℤ) < z
  apply DerivTot.seq (B := B.comp fun σ => σ + 1) _
    (DerivTot.assign (fun σ => σ + 1) B)
  apply DerivTot.conseq _ (DerivTot.unitary (regE n) (gate n) _) (Assn.le_refl' _)
  intro σ
  by_cases hp : True ∧ bGuard n σ = true ∧ (rank n σ : ℤ) = z
  · have hσ : σ < n := by simpa [bGuard] using hp.2.1
    have hlt : (rank n (σ + 1) : ℤ) < z := by
      simp only [rank] at hp ⊢
      omega
    rw [Assn.mask_op_of_pos (φ := fun σ =>
      True ∧ bGuard n σ = true ∧ (rank n σ : ℤ) = z) hp]
    refine Assn.le_op_of_eq_one ?_
    rw [Assn.unitaryPre_op_of_dist _ (regE n) (gate n) (distE n σ),
      Assn.comp_op]
    simp only [B, Assn.mask, if_pos hlt, Assn.one_op]
    rw [Module.End.one_eq_id, LinearMap.id_comp]
    exact (isUnitary_regLift ⟨regE n σ, distE n σ⟩ (gate n σ)).1
  · exact Assn.op_zero_le (Assn.mask_op_of_neg (φ := fun σ =>
      True ∧ bGuard n σ = true ∧ (rank n σ : ℤ) = z) hp)

/-- The source **(R-Loop-tot)**: separate invariant and identity-decrease
premises, with the natural counter rank embedded into the integers. -/
theorem loopDeriv :
    DerivTot (J n) (Prog.while (bGuard n) (body n)) ((J n).mandNot (bGuard n)) := by
  have hmask : (J n).mask (fun _ => True) = J n := by
    ext σ
    simp
  have hi : DerivTot (((J n).mask (fun _ => True)).mand (bGuard n))
      (body n) ((J n).mask (fun _ => True)) := by
    simpa only [hmask] using bodyInvariantDeriv n
  have h := DerivTot.whileLoopSource (A := J n) (φ := fun _ => True)
    (fun σ => (rank n σ : ℤ)) (fun _ _ => Int.natCast_nonneg _) hi
    (bodyIdentityRankDeriv n)
  simpa only [hmask] using h

theorem pre_le : P0 n ≤ (J n).comp fun _ => 0 := by
  intro σ
  exact le_of_eq (by rw [P0_op, Assn.comp_op, J_op, plusAt_zero])

theorem post_le : (J n).mandNot (bGuard n) ≤ Pplus n := by
  intro σ
  by_cases hg : bGuard n σ = true
  · exact Assn.op_zero_le (Assn.mandNot_op_of_true (A := J n) (b := bGuard n) (σ := σ) hg)
  · have hσ : n ≤ σ := by simpa [bGuard] using hg
    refine le_of_eq ?_
    rw [Assn.mandNot_op_of_false (A := J n) (b := bGuard n) (σ := σ) (by simpa using hg),
      J_op, Pplus_op, plusAt_of_ge n hσ, plusAt_top]

/-- **L-7f**: `{⊗ᵢ ∣0⟩⟨0∣} i := 0; while i < n do x[i] *= H; i := i + 1 od
{⊗ᵢ ∣+⟩⟨+∣}` is derivable in `QHL⁺_tot` — CoqQ's `RS_ParaHadamard_tuple0`. -/
theorem phDeriv : DerivTot (P0 n) (phProg n) (Pplus n) :=
  DerivTot.conseq (pre_le n)
    (DerivTot.seq (DerivTot.assign (fun _ => 0) (J n)) (loopDeriv n))
    (post_le n)

/-- **The semantic content**, through soundness (L-4): all the mass of a state
in `⊗ᵢ ∣0⟩` terminates, in `⊗ᵢ ∣+⟩`. -/
theorem phValid : validTot (P0 n) (phProg n) (Pplus n) := (phDeriv n).sound

end

/-! Both headline theorems are axiom-clean:
`[propext, Classical.choice, Quot.sound]`. -/
#print axioms Qhl.ParallelHadamardTriple.phDeriv
#print axioms Qhl.ParallelHadamardTriple.phValid

/-! ## §5. The sub-register-generic form (the derivation QPE consumes)

The derivation above is CoqQ's `RS_ParaHadamard_tuple0` on the standard
`n`-qubit world. A larger circuit reuses it **as a subroutine**: the same
counted Hadamard loop runs over the `n` cells a register `r : Reg L n` names
inside a bigger all-qubit world `L`, every unnamed cell carrying an arbitrary
unit frame factor `g` — the `{P} S {Q} ⊢ {P ⊗ R} S {Q ⊗ R}` shape of the
frame reuse (CoqQ `RV_Frame` / `QFT_sub_cast`: the recast is the reindexing
`r`), realised by generalising the derivation itself over the placement. The
loop is discharged by ONE `DerivTot.countedProdChainSource` call — printed
constructors only — along the interpolating family `phFamOn`, the
sub-register reading of `plusAt`. `Qhl/Examples/QPETriple.lean` consumes
`phDerivOn` at the counting register of the `(n+1)`-qubit world, the
eigenstate cell as the frame; the identity placement gives back the flagship
triple (the closing `example`). -/

section Generic

variable {L : Type*} [Fintype L] [DecidableEq L] {σT : Type*}
variable (n : ℕ) [NeZero n] (r : Reg L n)

/-- The interpolating family at the placement `r`: the first `m` named cells
already Hadamarded, the remaining named cells still `∣0⟩`, the frame `g`
untouched on every unnamed cell — `plusAt`, read on a sub-register. -/
noncomputable def phFamOn (g : L → 𝕢) (m : ℕ) : L → 𝕢 := fun i =>
  if h : i ∈ r.sig then
    (if ((r.equivSig.symm ⟨i, h⟩ : Fin n) : ℕ) < m then qplus else q0)
  else g i

/-- The family read at a named cell: the `j`-th cell of the placement. -/
theorem phFamOn_reg (g : L → 𝕢) (m : ℕ) (j : Fin n) :
    phFamOn n r g m (r j) = if (j : ℕ) < m then qplus else q0 := by
  have hmem : r j ∈ r.sig := r.apply_mem_sig j
  have hidx : r.equivSig.symm ⟨r j, hmem⟩ = j := by
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext (r.coe_equivSig j).symm
  simp only [phFamOn]
  rw [dif_pos hmem, hidx]

/-- The family off the placement: the frame factor. -/
theorem phFamOn_off (g : L → 𝕢) (m : ℕ) {i : L} (h : i ∉ r.sig) :
    phFamOn n r g m i = g i := by
  simp only [phFamOn]
  rw [dif_neg h]

/-- Every factor is a unit vector (the frame factors by hypothesis). -/
theorem norm_phFamOn (g : L → 𝕢) (hg : ∀ i, ‖g i‖ = 1) (m : ℕ) (i : L) :
    ‖phFamOn n r g m i‖ = 1 := by
  simp only [phFamOn]
  split
  · split
    · exact norm_qplus
    · exact norm_q0
  · exact hg i

/-- Entry: no named cell is Hadamarded yet. -/
theorem phFamOn_zero (g : L → 𝕢) :
    phFamOn n r g 0 = fun i => if i ∈ r.sig then q0 else g i := by
  funext i
  simp only [phFamOn]
  by_cases h : i ∈ r.sig
  · rw [dif_pos h, if_neg (Nat.not_lt_zero _), if_pos h]
  · rw [dif_neg h, if_neg h]

/-- Exit: every named cell is Hadamarded. -/
theorem phFamOn_full (g : L → 𝕢) :
    phFamOn n r g n = fun i => if i ∈ r.sig then qplus else g i := by
  funext i
  simp only [phFamOn]
  by_cases h : i ∈ r.sig
  · rw [dif_pos h, if_pos (r.equivSig.symm ⟨i, h⟩).isLt, if_pos h]
  · rw [dif_neg h, if_neg h]

/-- The touched cell still carries `∣0⟩`. -/
theorem phFamOn_ctrl (g : L → 𝕢) {k : ℕ} (hk : k < n) :
    phFamOn n r g k (r (cell n k)) = q0 := by
  rw [phFamOn_reg n r g k (cell n k), cell_val n hk, if_neg (lt_irrefl k)]

/-- One Hadamard advances the family — `K_plusAt`, read on a sub-register. -/
theorem phFamOn_step (g : L → 𝕢) {k : ℕ} (hk : k < n) :
    Function.update (phFamOn n r g k) (r (cell n k)) qplus
      = phFamOn n r g (k + 1) := by
  funext i
  by_cases hik : i = r (cell n k)
  · rw [hik, Function.update_self, phFamOn_reg n r g (k + 1) (cell n k), cell_val n hk,
      if_pos (Nat.lt_succ_self k)]
  · rw [Function.update_of_ne hik]
    by_cases hmem : i ∈ r.sig
    · obtain ⟨j₀, rfl⟩ := Reg.mem_sig.mp hmem
      have hjk : (j₀ : ℕ) ≠ k := fun hc =>
        hik (congrArg r (Fin.ext (hc.trans (cell_val n hk).symm)))
      simp only [phFamOn_reg n r g,
        show ((j₀ : ℕ) < k + 1) = ((j₀ : ℕ) < k) from by
          simp only [eq_iff_iff]; omega]
    · rw [phFamOn_off n r g k hmem, phFamOn_off n r g (k + 1) hmem]

variable (c : CounterLens σT)

/-- The register expression of the generic loop: the store-read counted cell,
placed by `r` (the paper's `q̄(t̄)`). -/
def phRegOn : RegExpr σT L 1 := fun σ => (Reg.single (r (cell n (c.get σ)))).toFun

/-- The Hadamard on the store-read placed cell. -/
noncomputable def phGateOn (σ : σT) :
    UnitaryOp (TSpace (QubitCells L) (phRegOn n r c σ)) :=
  singleGate (QubitCells L) (r (cell n (c.get σ))) H

/-- The generic counted parallel-Hadamard loop at the placement `r`:
`cnt := 0 ; while cnt < n do q[r (cell cnt)] *= H ; cnt := cnt + 1 od`. -/
noncomputable def phProgOn : Prog σT (QubitCells L) :=
  countedProg c (fun _ => n) (.unitary 1 (phRegOn n r c) (phGateOn n r c))

/-- **The sub-register-generic parallel-Hadamard derivation**: at any placement
`r` of `n` cells inside any all-qubit world `L`, over any counter lens and any
unit frame `g` on the unnamed cells,

```
⊢ₜ { ∣0⟩^r ⊗ g }  phProgOn r  { (∣+⟩^r ⊗ g) ∧ cnt = n }.
```

ONE call of the source counted-loop rule (`DerivTot.countedProdChainSource`)
along `phFamOn`, with separate invariant-preservation and identity-predicate
body derivations. This is the generic source-rule proof reused by QPE.
Each pass is one one-cell rung
(`DerivTot.countedRung_single`) whose action facts are `phFamOn_ctrl`, `H_q0`
and `phFamOn_step`. The frame `g` rides through every rung untouched — the
subroutine-reuse shape of the charter's §Subroutine REUSE. -/
theorem phDerivOn (g : L → 𝕢) (hg : ∀ i, ‖g i‖ = 1) :
    DerivTot (σT := σT)
      (prodA (QubitCells L) (phFamOn n r g 0) (norm_phFamOn n r g hg 0))
      (phProgOn n r c)
      ((prodA (QubitCells L) (phFamOn n r g n) (norm_phFamOn n r g hg n)).mask
        fun σ => c.get σ = n) :=
  DerivTot.countedProdChainSource c (phFamOn n r g) (norm_phFamOn n r g hg) rfl rfl
    (DerivTot.countedRung_single_fam (phRegOn n r c) (phGateOn n r c)
      (fun σ => r (cell n (c.get σ))) (fun _ => H)
      (fun σ => norm_phFamOn n r g hg (c.get σ))
      (fun σ => norm_phFamOn n r g hg (c.get σ + 1))
      (fun σ _ => ⟨(Reg.single (r (cell n (c.get σ)))).inj, rfl⟩)
      (fun σ hσ => by
        rw [phFamOn_ctrl n r g hσ, H_q0]
        exact phFamOn_step n r g hσ))
    (fun _ => DerivTot.unitary_identity_mask (phRegOn n r c) (phGateOn n r c)
      (fun σ _ => (Reg.single (r (cell n (c.get σ)))).inj))

end Generic

/-- **The identity-placement instantiation is the flagship triple**: `phDerivOn`
at the full register `Fin n` (trivial frame), with the endpoints recast by
(R-Conseq), re-derives the statement of `phDeriv` — the generic form really is
a generalisation of the derivation above. -/
example (n : ℕ) [NeZero n] : DerivTot (P0 n) (phProg n) (Pplus n) := by
  have h0 : phFamOn n (⟨fun i => i, fun _ _ h => h⟩ : Reg (QubitL n) n) (fun _ => q0) 0
      = fun _ : QubitL n => q0 := by
    funext i
    simp only [phFamOn]
    split
    · rw [if_neg (Nat.not_lt_zero _)]
    · rfl
  have h1 : phFamOn n (⟨fun i => i, fun _ _ h => h⟩ : Reg (QubitL n) n) (fun _ => q0) n
      = fun _ : QubitL n => qplus := by
    funext i
    simp only [phFamOn]
    rw [dif_pos (Reg.mem_sig.mpr ⟨i, rfl⟩), if_pos (Fin.isLt _)]
  refine DerivTot.conseq (fun σ => le_of_eq ?_)
    (phDerivOn n (⟨fun i => i, fun _ _ h => h⟩ : Reg (QubitL n) n) CounterLens.nat
      (fun _ => q0) (fun _ => norm_q0))
    (Assn.mask_le_of_imp_le fun σ _ => le_of_eq ?_)
  · rw [P0_op, prodA_op, h0, allZeros, allZerosOn]
  · rw [prodA_op, Pplus_op, h1, allPlus, allPlusOn]

end Qhl.ParallelHadamardTriple

namespace Qhl.ParallelHadamardSource
open Finset
open ParallelHadamardTriple

variable {L : Type*} [Fintype L] [DecidableEq L] {σT : Type*}

/-- The generic placed parallel-Hadamard program, with its exact final counter. -/
theorem phDerivOn (n : ℕ) [NeZero n] (r : Reg L n) (c : CounterLens σT)
    (g : L → 𝕢) (hg : ∀ i, ‖g i‖ = 1) :
    SourceDerivTot (σT := σT)
      (SourceAssertion.ofAssn
        (prodA (QubitCells L) (phFamOn n r g 0) (norm_phFamOn n r g hg 0))
        (fun _ => True))
      (phProgOn n r c)
      (SourceAssertion.ofAssn
        (prodA (QubitCells L) (phFamOn n r g n) (norm_phFamOn n r g hg n))
        (fun σ => c.get σ = n)) := by
  let v : σT → HS (QubitCells L) (univ : Finset L) := fun σ =>
    prodV (QubitCells L) (W := (univ : Finset L))
    (phFamOn n r g (c.get σ))
  let hv : ∀ σ, ‖v σ‖ = 1 := fun σ => norm_prodV_eq_one _ (norm_phFamOn n r g hg (c.get σ))
  let A : Assn σT (QubitCells L) := Assn.ofStateFam v hv
  have body : SourceDerivTot
      (SourceAssertion.ofAssn A (fun σ => True ∧ c.get σ < n))
      (.unitary 1 (phRegOn n r c) (phGateOn n r c))
      (SourceAssertion.ofAssn (A.comp (fun σ => c.set σ (c.get σ + 1)))
        (fun σ => True ∧ c.get σ < n)) := by
    change SourceDerivTot (SourceAssertion.ofAssn (Assn.ofStateFam v hv) _) _
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ => v (c.set σ (c.get σ + 1)))
        (fun σ => hv (c.set σ (c.get σ + 1)))) _)
    apply SourceDerivTot.unitary_stateFam_guard (phRegOn n r c) (phGateOn n r c)
      v (fun σ => v (c.set σ (c.get σ + 1))) hv
      (fun σ => hv (c.set σ (c.get σ + 1))) (fun σ => True ∧ c.get σ < n)
      (fun σ _ => (Reg.single (r (cell n (c.get σ)))).inj)
    · intro σ hσ
      change regLift (D := QubitCells L) (Reg.single (r (cell n (c.get σ))))
        (singleGate (QubitCells L) (r (cell n (c.get σ))) H)
        (prodV (QubitCells L) (phFamOn n r g (c.get σ))) = _
      rw [regLift_singleGate_prodV]
      simp only [v, c.get_set]
      rw [phFamOn_ctrl n r g hσ.2, H_q0, phFamOn_step n r g hσ.2]
  have h := SourceDerivTot.countedWhile c (fun _ => n) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) A
    (.unitary 1 (phRegOn n r c) (phGateOn n r c)) body
    (fun z => SourceDerivTot.unitary_identity _ _ _
      (fun σ _ => (Reg.single (r (cell n (c.get σ)))).inj))
  refine SourceDerivTot.conseq ?_ h ?_
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      apply le_of_eq
      simp [A, v, Assn.comp, Assn.ofStateFam_op, prodA_op, c.get_set]
  · apply SourceAssertion.entails_ofAssn
    · intro σ hσ; exact hσ.2
    · intro σ hσ
      apply le_of_eq
      simp [A, v, Assn.ofStateFam_op, prodA_op, hσ.2]

/-- The generic placed parallel-Hadamard program, with its exact final counter. -/
theorem phDerivOnWith (n : ℕ) [NeZero n] (r : Reg L n) (c : CounterLens σT)
    (g : L → 𝕢) (hg : ∀ i, ‖g i‖ = 1)
    (φ : σT → Prop) (hφ : ∀ σ k, φ (c.set σ k) ↔ φ σ) :
    SourceDerivTot (σT := σT)
      (SourceAssertion.ofAssn
        (prodA (QubitCells L) (phFamOn n r g 0) (norm_phFamOn n r g hg 0))
        φ)
      (phProgOn n r c)
      (SourceAssertion.ofAssn
        (prodA (QubitCells L) (phFamOn n r g n) (norm_phFamOn n r g hg n))
        (fun σ => φ σ ∧ c.get σ = n)) := by
  let v : σT → HS (QubitCells L) (univ : Finset L) := fun σ =>
    prodV (QubitCells L) (W := (univ : Finset L))
    (phFamOn n r g (c.get σ))
  let hv : ∀ σ, ‖v σ‖ = 1 := fun σ => norm_prodV_eq_one _ (norm_phFamOn n r g hg (c.get σ))
  let A : Assn σT (QubitCells L) := Assn.ofStateFam v hv
  have body : SourceDerivTot
      (SourceAssertion.ofAssn A (fun σ => φ σ ∧ c.get σ < n))
      (.unitary 1 (phRegOn n r c) (phGateOn n r c))
      (SourceAssertion.ofAssn (A.comp (fun σ => c.set σ (c.get σ + 1)))
        (fun σ => φ σ ∧ c.get σ < n)) := by
    change SourceDerivTot (SourceAssertion.ofAssn (Assn.ofStateFam v hv) _) _
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ => v (c.set σ (c.get σ + 1)))
        (fun σ => hv (c.set σ (c.get σ + 1)))) _)
    apply SourceDerivTot.unitary_stateFam_guard (phRegOn n r c) (phGateOn n r c)
      v (fun σ => v (c.set σ (c.get σ + 1))) hv
      (fun σ => hv (c.set σ (c.get σ + 1))) (fun σ => φ σ ∧ c.get σ < n)
      (fun σ _ => (Reg.single (r (cell n (c.get σ)))).inj)
    · intro σ hσ
      change regLift (D := QubitCells L) (Reg.single (r (cell n (c.get σ))))
        (singleGate (QubitCells L) (r (cell n (c.get σ))) H)
        (prodV (QubitCells L) (phFamOn n r g (c.get σ))) = _
      rw [regLift_singleGate_prodV]
      simp only [v, c.get_set]
      rw [phFamOn_ctrl n r g hσ.2, H_q0, phFamOn_step n r g hσ.2]
  have h := SourceDerivTot.countedWhile c (fun _ => n) φ
    hφ (fun _ _ => rfl) A
    (.unitary 1 (phRegOn n r c) (phGateOn n r c)) body
    (fun z => SourceDerivTot.unitary_identity _ _ _
      (fun σ _ => (Reg.single (r (cell n (c.get σ)))).inj))
  refine SourceDerivTot.conseq ?_ h ?_
  · apply SourceAssertion.entails_ofAssn
    · intro _ h; exact h
    · intro σ _
      apply le_of_eq
      simp [A, v, Assn.comp, Assn.ofStateFam_op, prodA_op, c.get_set]
  · apply SourceAssertion.entails_ofAssn
    · intro σ hσ; exact hσ
    · intro σ hσ
      apply le_of_eq
      simp [A, v, Assn.ofStateFam_op, prodA_op, hσ.2]

/-- The original whole-register program and its original True/projector endpoints. -/
theorem phDeriv (n : ℕ) [NeZero n] : SourceDerivTot
    (SourceAssertion.ofAssn (P0 n) (fun _ => True)) (phProg n)
    (SourceAssertion.ofAssn (Pplus n) (fun _ => True)) := by
  let r : Reg (QubitL n) n := ⟨fun i => i, fun _ _ h => h⟩
  have h0 : phFamOn n r (fun _ => q0) 0 = fun _ : QubitL n => q0 := by
    funext i
    simp only [phFamOn]
    split
    · rw [if_neg (Nat.not_lt_zero _)]
    · rfl
  have h1 : phFamOn n r (fun _ => q0) n = fun _ : QubitL n => qplus := by
    funext i
    simp only [phFamOn]
    rw [dif_pos (Reg.mem_sig.mpr ⟨i, rfl⟩), if_pos (Fin.isLt _)]
  refine SourceDerivTot.conseq ?_
    (phDerivOn n r CounterLens.nat (fun _ => q0) (fun _ => norm_q0)) ?_
  · apply SourceAssertion.entails_ofAssn
    · intro _ _; trivial
    · intro σ _
      apply le_of_eq
      rw [P0_op, prodA_op, h0, allZeros, allZerosOn]
  · apply SourceAssertion.entails_ofAssn
    · intro _ _; trivial
    · intro σ _
      apply le_of_eq
      rw [prodA_op, Pplus_op, h1, allPlus, allPlusOn]

/-- Compatibility with the exact pre-existing semantic triple, through source soundness. -/
theorem phValid (n : ℕ) [NeZero n] : validTot (P0 n) (phProg n) (Pplus n) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (phDeriv n).sound

/-- The generic source derivation interprets to the existing counter-masked triple. -/
theorem phValidOn (n : ℕ) [NeZero n] (r : Reg L n) (c : CounterLens σT)
    (g : L → 𝕢) (hg : ∀ i, ‖g i‖ = 1) :
    validTot
      (prodA (QubitCells L) (phFamOn n r g 0) (norm_phFamOn n r g hg 0))
      (phProgOn n r c)
      ((prodA (QubitCells L) (phFamOn n r g n) (norm_phFamOn n r g hg n)).mask
        fun σ => c.get σ = n) := by
  have h := (phDerivOn n r c g hg).sound
  rw [SourceAssertion.toAssn_ofAssn_true] at h
  simpa only [SourceAssertion.toAssn_ofAssn] using h

end Qhl.ParallelHadamardSource
