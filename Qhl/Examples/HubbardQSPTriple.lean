import Qhl.Logic.Source.CountedStateChain
import Qhl.Logic.Source.ProductStateFam
import Qhl.Logic.Soundness
import Qhl.Logic.StateFamGuard
import Qhl.Logic.CountedStateChain
import Qhl.Program.StoreLens
import Qhl.Register.Qubitization
import Qhl.Examples.HubbardLCUTriple

/-!
# Quantum-signal-processing simulation on the Hubbard block encoding

The qubitization/QSP Hamiltonian-simulation loop (Low–Chuang, *Hamiltonian
simulation by qubitization*, Quantum 3, 163 (2019), arXiv:1610.06546;
Gilyén–Su–Low–Wiebe, arXiv:1806.01838) built on the LCU block encoding of the
Bravyi–Kitaev Fermi–Hubbard Hamiltonian (`Qhl/Examples/HubbardLCUTriple.lean`):

```
k := 0;
while k < d do
  a₀ *= phase(φ k);                 -- the QSP phase, on the single cell a₀
  prep ; select ; unprep;           -- the lane-(iii) block-encoding fragments
  a₀ *= Z;                          -- the reflection, on the single cell a₀
  k := k + 1
od
```

over the classical store `σ = (σc, φ, k)`: the lane-(iii) widened store
`σc : STc = ℕ × ℕ × (t, U)` (its two loop counters and the Hamiltonian
coefficients), the **classical angle array** `φ : Fin d → ℝ` and the QSP loop
counter.  Every gate is constant-arity (one or two cells); all `n`- and
`d`-dependence lives in the loop structure, and the phase angle of pass `k`
is computed from the store (the paper's parameterized-gate feature).  The
`prep`/`select`/`unprep` fragments are the lane-(iii) **programs**, reused
verbatim through the store lens `StoreLens.fst`
(`Qhl/Program/StoreLens.lean`) — they are composed by `.seq`, not packaged as
one unitary.  Each fragment is a genuine counted `while`
(`countedProg`, `Qhl/Logic/CountedWhile.lean`); the transport along the lens
is definitional (`Prog.mapStore_countedProg`), the transported counter lenses
are `CounterLens.pullbackFst` of the lane-(iii) lenses, and inside the ranked
QSP loop each fragment loop is discharged by **one**
`DerivTot.countedStateChain_rel` call (`Qhl/Logic/CountedStateChain.lean`)
along a `chainPre` prefix family over the walker state the pass carries —
no `for`-fold anywhere.

**The reflection realization (constant arity).**  The reflection about
`∣0⟩ₐ` is realized by the **one-cell Pauli `Z` gate on ancilla cell `a₀`** —
no `k`-cell primitive, no extra flag cells.  This is exact on the walker's
invariant subspace, and that is proved, not assumed: in the unary (one-hot)
LCU architecture the walk output `U(∣0⟩ₐ ⊗ ψ)` decomposes as its
ancilla-vacuum component plus components whose ancilla patterns all have
**cell `a₀` set** (the `X(a₀)` of `unprep` carries the one-hot sector to
vacuum ⊕ two-hot-`{a₀, i}` patterns — `outSt_wk` below), so `Z(a₀)` agrees
with `2∣0⟩⟨0∣ₐ − 1` on every state the loop reaches from the block
(`refl_outSt`).  Likewise the QSP phase is the one-cell gate
`phase φ = diag(1, e^{iφ})` on `a₀`, which acts on the walker block as
`diag(1, e^{iφ})` — the standard `e^{iφZ}` form up to the usual global-phase
convention (see `Qhl/Register/Qubitization.lean`).

Deliverables, in three tiers (all loop reasoning by the printed `QHL⁺_tot`
rules only — (Ax-Uni), (Ax-Ass), (R-Seq), (R-Conseq) and the ranked
(R-Loop-tot): rank `d − k` for the QSP loop, and the counted-`while` layer —
itself (Ax-Ass)+(R-Loop-tot)+(R-Conseq) — for the fragment loops):

* **Tier 1** `qspDeriv` / `qspValid` — the exact evolution triple
  `{ ∣0⟩ₐ ⊗ ψ } qspProg { ∣Ξ_out⟩ }`: the loop implements exactly the
  alternating product `∏_{k<d} (refl ∘ lcu ∘ phase(φ k))` applied to the
  input, the named output `qspSt … d` (the loop invariant is the partial
  product applied to the input state); `qspPre_expect_one` — non-vacuity.
* **Tier 2** `hubbard_qubitization` / `hubbard_walk_rot_emb` /
  `hubbard_walk_rot_u1` — for a unit eigenvector `v` of `hubbardOp` with
  eigenvalue `E` (`|E| < λ`), the 2D subspace spanned by `∣0⟩ₐ ⊗ v` and the
  orthogonal partner of the walk image is invariant under the reflection and
  the walk, and the reflected walk acts on it as the rotation with
  `cos = E/λ`; `hubbard_qsp_product` — the blockwise 2×2 QSP matrix product
  identity for arbitrary phases (`Qhl/Register/Qubitization.lean`).
* **Tier 3** `hubbard_qsp_transfer` — the hypothesis-carrying transfer
  corollary: if the QSP product entry `P_φ(E/λ)` is `ε`-close to a target,
  the post-selected output component is `ε`-close to `target • v`.  (The
  existence of angle sequences realizing a given target polynomial —
  Jacobi–Anger expansions etc. — is *not* formalized; it is the
  angle-synthesis result of the papers cited above.)
-/

namespace Qhl.HubbardQSP

open Qhl Qhl.HubbardLCU Qhl.BravyiKitaev Finset
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal

section

variable (x : ℕ) (hx : 0 < x) (d : ℕ)

/-! ## §1. The classical store: the widened LCU store, angle array, counter -/

/-- The store: the lane-(iii) widened store `STc = ℕ × ℕ × (t, U)` (its loop
counters and the Hamiltonian coefficients), the QSP angle array, and the QSP
loop counter.  The LCU fragments run on the first component through
`StoreLens.fst`. -/
abbrev STQc : Type := STc × (Fin d → ℝ) × ℕ

/-- The QSP loop counter. -/
def cnt (σ : STQc d) : ℕ := σ.2.2

/-- The angle array. -/
def phis (σ : STQc d) : Fin d → ℝ := σ.2.1

/-- The Hamiltonian coefficient block, read through the lane-(iii) accessor
`coef` of the embedded widened store. -/
abbrev coefQ (σ : STQc d) : ST := coef σ.1

/-- The angle array padded to `ℕ` (angle `0` beyond `d`; the loop never reads
the padding). -/
def phiSeq (Φ : Fin d → ℝ) : ℕ → ℝ := fun m => if h : m < d then Φ ⟨m, h⟩ else 0

/-- The phase angle of the current pass, read from the store. -/
def phiAt (σ : STQc d) : ℝ := phiSeq d (phis d σ) (cnt d σ)

/-! ## §2. The program -/

/-- The lane-(iii) PREPARE fragment, over the enlarged store. -/
noncomputable def prepQ : Prog (STQc d) (QubitCells (WL x)) :=
  (prepProg x hx).mapStore StoreLens.fst

/-- The lane-(iii) SELECT fragment, over the enlarged store. -/
noncomputable def selQ : Prog (STQc d) (QubitCells (WL x)) :=
  (selProg x hx).mapStore StoreLens.fst

/-- The lane-(iii) UNPREPARE fragment, over the enlarged store. -/
noncomputable def unprepQ : Prog (STQc d) (QubitCells (WL x)) :=
  (unprepProg x hx).mapStore StoreLens.fst

/-- The reflection about `∣0⟩ₐ` on the walker subspace: the one-cell Pauli
`Z` gate on ancilla cell `a₀`. -/
noncomputable def reflProg : Prog (STQc d) (QubitCells (WL x)) :=
  Prog.unitary 1 (RegExpr.const (Reg.single (aC x (a0 x hx))))
    (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) Z)

/-- The QSP phase gate of the current pass: `phase(φ k)` on ancilla cell
`a₀`, the angle computed from the store. -/
noncomputable def phaseProg : Prog (STQc d) (QubitCells (WL x)) :=
  Prog.unitary 1 (RegExpr.const (Reg.single (aC x (a0 x hx))))
    (fun σ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) (phase (phiAt d σ)))

/-- One walk pass: the block-encoding fragments, then the reflection. -/
noncomputable def wPassProg : Prog (STQc d) (QubitCells (WL x)) :=
  (prepQ x hx d).seq ((selQ x hx d).seq ((unprepQ x hx d).seq (reflProg x hx d)))

/-- The loop guard `k < d`. -/
def gdQ (σ : STQc d) : Bool := decide (cnt d σ < d)

/-- The loop body: the phase gate, the walk pass, `k := k + 1`. -/
noncomputable def bodyProg : Prog (STQc d) (QubitCells (WL x)) :=
  ((phaseProg x hx d).seq (wPassProg x hx d)).seq
    (Prog.assign fun σ : STQc d => (σ.1, σ.2.1, σ.2.2 + 1))

/-- **The QSP program** `k := 0; while k < d do phase; W-pass; k := k+1 od`. -/
noncomputable def qspProg : Prog (STQc d) (QubitCells (WL x)) :=
  (Prog.assign fun σ : STQc d => (σ.1, σ.2.1, 0)).seq
    (Prog.while (gdQ d) (bodyProg x hx d))

/-! ## §3. The mapped fragments: counted loops over the pulled-back lenses

The lane-(iii) fragments are counted `while` loops over the counter lenses of
the widened store; the transport along `StoreLens.fst` is definitional
(`Prog.mapStore_countedProg`), so each mapped fragment **is** the counted
loop of the mapped body over the pulled-back lens — every equation below is
`rfl`. -/

/-- The lane-(iii) outer counter, pulled back to the enlarged store. -/
def cOuterQ : CounterLens (STQc d) := CounterLens.pullbackFst (CounterLens.fst3 ST)

/-- The lane-(iii) inner (letter) counter, pulled back. -/
def cInnerQ : CounterLens (STQc d) := CounterLens.pullbackFst (CounterLens.snd3 ST)

theorem prepQ_eq :
    prepQ x hx d
      = (Prog.unitary 1 (RegExpr.const (Reg.single (aC x (a0 x hx))))
          (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)).seq
        (countedProg (cOuterQ d) (fun _ => HubbardLCU.NT x - 1)
          ((prepBody x hx).mapStore StoreLens.fst)) := rfl

theorem selQ_eq :
    selQ x hx d
      = countedProg (cOuterQ d) (fun _ => HubbardLCU.NT x)
          (((sgnBody x hx).mapStore StoreLens.fst).seq
            (countedProg (cInnerQ d) (fun _ => 2 ^ x)
              ((ctrlBody x hx).mapStore StoreLens.fst))) := rfl

theorem unprepQ_eq :
    unprepQ x hx d
      = (countedProg (cOuterQ d) (fun _ => HubbardLCU.NT x - 1)
          ((unprepBody x hx).mapStore StoreLens.fst)).seq
        (Prog.unitary 1 (RegExpr.const (Reg.single (aC x (a0 x hx))))
          (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)) := rfl

/-! ## §4. The semantic operators of the fragments -/

/-- The PREPARE Givens-chain operator (the semantic operator of the
lane-(iii) chain, `adjoint_unprepChain`'s right-hand side). -/
noncomputable def prepChain (τ : ST) : EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  chainOp (List.finRange (HubbardLCU.NT x - 1))
    (fun j => regLift (prepReg x j)
      ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
        (jA_ne_jB x j) (givens (ang x hx τ (j : ℕ) (jA_lt x j)))) :
        TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _))

/-- The sign gate of rung `l`, lifted. -/
noncomputable def sgnL (τ : ST) (l : AncL x) : EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  regLift (Reg.single (aC x l))
    ((singleGate (QubitCells (WL x)) (aC x l) (sgnGate (cf x τ l)) :
      UnitaryOp (TSpace (QubitCells (WL x)) (Reg.single (aC x l)).toFun)) :
      TSpace (QubitCells (WL x)) (Reg.single (aC x l)).toFun →ₗ[ℂ] _)

/-- The controlled-letter chain of rung `l`, lifted. -/
noncomputable def ctrlChain (l : AncL x) : EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  chainOp (List.finRange (2 ^ x))
    (fun s => regLift (ctrlReg x l s)
      ((pairGate (D := QubitCells (WL x)) (aC x l) (sC x s) Sum.inr_ne_inl
        (control (str x l s).gate)) :
        TSpace (QubitCells (WL x)) (ctrlReg x l s).toFun →ₗ[ℂ] _))

/-- The full rung `l`: sign gate, then the letter chain. -/
noncomputable def rungOp (τ : ST) (l : AncL x) : EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  ctrlChain x l ∘ₗ sgnL x τ l

/-- The SELECT operator after `l` rungs. -/
noncomputable def selPart (τ : ST) : ℕ → EndM (QubitCells (WL x)) (univ : Finset (WL x))
  | 0 => 1
  | l + 1 => if h : l < HubbardLCU.NT x then rungOp x τ ⟨l, h⟩ ∘ₗ selPart τ l else selPart τ l

theorem selPart_succ (τ : ST) (l : ℕ) (h : l < HubbardLCU.NT x) :
    selPart x τ (l + 1) = rungOp x τ ⟨l, h⟩ ∘ₗ selPart x τ l := by
  show (if h : l < HubbardLCU.NT x then rungOp x τ ⟨l, h⟩ ∘ₗ selPart x τ l else selPart x τ l) = _
  rw [dif_pos h]

/-- The full SELECT operator. -/
noncomputable def selOp (τ : ST) : EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  selPart x τ (HubbardLCU.NT x)

/-- The reflection operator: `Z` on ancilla cell `a₀`. -/
noncomputable def reflOp : EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  gateAt (WL x) (aC x (a0 x hx)) Z

/-- The phase operator: `phase φ` on ancilla cell `a₀`. -/
noncomputable def phOp (φ : ℝ) : EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  gateAt (WL x) (aC x (a0 x hx)) (phase φ)

/-- The semantic operator of one whole LCU pass `prep ; select ; unprep`. -/
noncomputable def lcuOp (τ : ST) : EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  ((xLift x hx ∘ₗ unprepChain x hx τ) ∘ₗ selOp x τ) ∘ₗ (prepChain x hx τ ∘ₗ xLift x hx)

theorem isUnitary_prepChain (τ : ST) : IsUnitary (prepChain x hx τ) :=
  isUnitary_chainOp _ _ fun _ => isUnitary_regLift _ _

theorem isUnitary_sgnL (τ : ST) (l : AncL x) : IsUnitary (sgnL x τ l) :=
  isUnitary_regLift _ _

theorem isUnitary_ctrlChain (l : AncL x) : IsUnitary (ctrlChain x l) :=
  isUnitary_chainOp _ _ fun _ => isUnitary_regLift _ _

theorem isUnitary_rungOp (τ : ST) (l : AncL x) : IsUnitary (rungOp x τ l) :=
  (isUnitary_ctrlChain x l).comp (isUnitary_sgnL x τ l)

theorem isUnitary_selPart (τ : ST) : ∀ l : ℕ, IsUnitary (selPart x τ l)
  | 0 => isUnitary_one
  | l + 1 => by
      by_cases h : l < HubbardLCU.NT x
      · rw [selPart_succ x τ l h]
        exact (isUnitary_rungOp x τ ⟨l, h⟩).comp (isUnitary_selPart τ l)
      · show IsUnitary (if h : l < HubbardLCU.NT x then _ else _)
        rw [dif_neg h]
        exact isUnitary_selPart τ l

theorem isUnitary_selOp (τ : ST) : IsUnitary (selOp x τ) := isUnitary_selPart x τ _

theorem isUnitary_reflOp : IsUnitary (reflOp x hx) := isUnitary_regLift _ _

theorem isUnitary_phOp (φ : ℝ) : IsUnitary (phOp x hx φ) := isUnitary_regLift _ _

theorem isUnitary_lcuOp (τ : ST) : IsUnitary (lcuOp x hx τ) :=
  ((((isUnitary_xLift x hx).comp (isUnitary_unprepChain x hx τ)).comp
    (isUnitary_selOp x τ)).comp
    ((isUnitary_prepChain x hx τ).comp (isUnitary_xLift x hx)))

/-! ## §5. The system embedding and the named iterate -/

/-- The system embedding `w ↦ ∣0⟩ₐ ⊗ w`. -/
noncomputable def sysEmb :
    HS (QubitCells (SysL x)) (univ : Finset (SysL x)) →ₗ[ℂ]
      HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  ancEmbed (L₁ := SysL x) (anc0 x)

variable (ψ : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))

/-- **The named state family of the loop**: after `m` passes with coefficients
`τ` and angles `Φ`, the alternating product
`∏_{k<m} (refl ∘ lcu ∘ phase(Φ k))` applied to `∣0⟩ₐ ⊗ ψ`
(`Qhl/Register/Qubitization.lean`, `qspIter`). -/
noncomputable def qspSt (τ : ST) (Φ : Fin d → ℝ) (m : ℕ) :
    HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  Qubitization.qspIter (sysEmb x) (lcuOp x hx τ) (reflOp x hx) (phOp x hx) ψ
    (phiSeq d Φ) m

variable (hψ : ‖ψ‖ = 1)

include hψ in
theorem norm_qspSt (τ : ST) (Φ : Fin d → ℝ) (m : ℕ) : ‖qspSt x hx d ψ τ Φ m‖ = 1 := by
  induction m with
  | zero =>
      rw [qspSt, Qubitization.qspIter_zero]
      exact norm_inS x ψ hψ
  | succ m ih =>
      rw [qspSt, Qubitization.qspIter_succ]
      exact norm_eq_one_of_isUnitary
        ((isUnitary_reflOp x hx).comp ((isUnitary_lcuOp x hx τ).comp
          (isUnitary_phOp x hx _))) ih

/-! ## §6. The loop-body stage families -/

/-- The loop-invariant state family, read at the raw counter: the partial
product after `k` passes.  The invariant masks the family by `k ≤ d` (the
counted-while mask pattern); the family is never read off the mask. -/
noncomputable def st0 (σ : STQc d) : HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  qspSt x hx d ψ (coefQ d σ) (phis d σ) (cnt d σ)

/-- After the phase gate. -/
noncomputable def st1 (σ : STQc d) : HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  phOp x hx (phiAt d σ) (st0 x hx d ψ σ)

/-- After the PREPARE `X` gate. -/
noncomputable def st2 (σ : STQc d) : HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  xLift x hx (st1 x hx d ψ σ)

/-- After the PREPARE Givens chain. -/
noncomputable def st3 (σ : STQc d) : HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  prepChain x hx (coefQ d σ) (st2 x hx d ψ σ)

/-- After `l` SELECT rungs. -/
noncomputable def stSel (l : ℕ) (σ : STQc d) : HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  selPart x (coefQ d σ) l (st3 x hx d ψ σ)

/-- After the UNPREPARE Givens chain. -/
noncomputable def st5 (σ : STQc d) : HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  unprepChain x hx (coefQ d σ) (stSel x hx d ψ (HubbardLCU.NT x) σ)

/-- After the UNPREPARE `X` gate. -/
noncomputable def st6 (σ : STQc d) : HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  xLift x hx (st5 x hx d ψ σ)

/-- After the reflection: one whole phased pass applied. -/
noncomputable def st7 (σ : STQc d) : HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  reflOp x hx (st6 x hx d ψ σ)

include hψ in
theorem norm_st0 (σ : STQc d) : ‖st0 x hx d ψ σ‖ = 1 :=
  norm_qspSt x hx d ψ hψ _ _ _

include hψ in
theorem norm_st1 (σ : STQc d) : ‖st1 x hx d ψ σ‖ = 1 :=
  norm_eq_one_of_isUnitary (isUnitary_phOp x hx _) (norm_st0 x hx d ψ hψ σ)

include hψ in
theorem norm_st2 (σ : STQc d) : ‖st2 x hx d ψ σ‖ = 1 :=
  norm_eq_one_of_isUnitary (isUnitary_xLift x hx) (norm_st1 x hx d ψ hψ σ)

include hψ in
theorem norm_st3 (σ : STQc d) : ‖st3 x hx d ψ σ‖ = 1 :=
  norm_eq_one_of_isUnitary (isUnitary_prepChain x hx _) (norm_st2 x hx d ψ hψ σ)

include hψ in
theorem norm_stSel (l : ℕ) (σ : STQc d) : ‖stSel x hx d ψ l σ‖ = 1 :=
  norm_eq_one_of_isUnitary (isUnitary_selPart x _ l) (norm_st3 x hx d ψ hψ σ)

include hψ in
theorem norm_st5 (σ : STQc d) : ‖st5 x hx d ψ σ‖ = 1 :=
  norm_eq_one_of_isUnitary (isUnitary_unprepChain x hx _)
    (norm_stSel x hx d ψ hψ (HubbardLCU.NT x) σ)

include hψ in
theorem norm_st6 (σ : STQc d) : ‖st6 x hx d ψ σ‖ = 1 :=
  norm_eq_one_of_isUnitary (isUnitary_xLift x hx) (norm_st5 x hx d ψ hψ σ)

include hψ in
theorem norm_st7 (σ : STQc d) : ‖st7 x hx d ψ σ‖ = 1 :=
  norm_eq_one_of_isUnitary (isUnitary_reflOp x hx) (norm_st6 x hx d ψ hψ σ)

/-! ## §6b. The prefix families of the counted fragment loops

Each fragment loop is discharged by one `DerivTot.countedStateChain_rel`
call along a `chainPre` prefix family (`Qhl/Logic/WpChain.lean` §5b): after
`k` passes the state is the prefix of the first `k` gates applied to the
walker state the pass entered with (the lane-(iii) `unprepSt` idiom, at the
arbitrary walker states of this loop).  The body-action facts read the gate
position from the stored counter through the total `jCell`/`lCell`/`sCell`
conversions, exactly as the lane-(iii) `*Body_act` facts do. -/

/-- The PREPARE prefix family: the first `m` Givens gates applied to the
post-`X` state. -/
noncomputable def prepPreQ (m : ℕ) (σ : STQc d) :
    HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  chainPre (List.finRange (HubbardLCU.NT x - 1))
    (fun j => regLift (prepReg x j)
      ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
        (jA_ne_jB x j) (givens (ang x hx (coefQ d σ) (j : ℕ) (jA_lt x j)))) :
        TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _))
    m (st2 x hx d ψ σ)

include hψ in
theorem norm_prepPreQ (m : ℕ) (σ : STQc d) : ‖prepPreQ x hx d ψ m σ‖ = 1 :=
  norm_eq_one_of_isUnitary
    (isUnitary_chainOp ((List.finRange (HubbardLCU.NT x - 1)).take m) _
      fun _ => isUnitary_regLift _ _)
    (norm_st2 x hx d ψ hψ σ)

/-- The full PREPARE prefix is the Givens chain: the loop exits at `st3`. -/
theorem prepPreQ_full (σ : STQc d) :
    prepPreQ x hx d ψ (HubbardLCU.NT x - 1) σ = st3 x hx d ψ σ := by
  have hlen : (List.finRange (HubbardLCU.NT x - 1)).length = HubbardLCU.NT x - 1 :=
    List.length_finRange
  have h := chainPre_length (List.finRange (HubbardLCU.NT x - 1))
    (fun j => regLift (prepReg x j)
      ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
        (jA_ne_jB x j) (givens (ang x hx (coefQ d σ) (j : ℕ) (jA_lt x j)))) :
        TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _))
  rw [hlen] at h
  rw [prepPreQ, h]
  rfl

/-- One PREPARE pass advances the prefix chain (concrete registers). -/
theorem prepPreQ_step (σ : STQc d) (k : ℕ) (hk : k < HubbardLCU.NT x - 1) :
    regLift (prepReg x (jCell x hx k))
        ((pairGate (D := QubitCells (WL x)) (aC x (jA x (jCell x hx k)))
          (aC x (jB x (jCell x hx k))) (jA_ne_jB x (jCell x hx k))
          (givens (ang x hx (coefQ d σ) ((jCell x hx k : Fin (HubbardLCU.NT x - 1)) : ℕ)
            (jA_lt x (jCell x hx k))))) :
          TSpace (QubitCells (WL x)) (prepReg x (jCell x hx k)).toFun →ₗ[ℂ] _)
        (prepPreQ x hx d ψ k σ)
      = prepPreQ x hx d ψ (k + 1) σ := by
  rw [jCell_eq_mk x hx hk, prepPreQ, prepPreQ, chainPre_finRange_succ _ hk,
    LinearMap.comp_apply]

/-- The PREPARE body acts, at the stored counter. -/
theorem prepBodyQ_act (σ : STQc d) (k : ℕ) (hσ1 : σ.1.1 = k)
    (hk : k < HubbardLCU.NT x - 1) :
    ∃ hinj : Function.Injective (prepRegE x hx σ.1),
      regLift ⟨prepRegE x hx σ.1, hinj⟩ (prepGateE x hx σ.1)
        (prepPreQ x hx d ψ k σ)
      = prepPreQ x hx d ψ (k + 1) σ := by
  subst hσ1
  exact ⟨(prepReg x (jCell x hx σ.1.1)).inj,
    prepPreQ_step x hx d ψ σ σ.1.1 hk⟩

/-- The mid-rung walker state: the sign gate of rung `l` applied. -/
noncomputable def sgnMidQ (l : ℕ) (σ : STQc d) :
    HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  sgnL x (coefQ d σ) (lCell x hx l) (stSel x hx d ψ l σ)

include hψ in
theorem norm_sgnMidQ (l : ℕ) (σ : STQc d) : ‖sgnMidQ x hx d ψ l σ‖ = 1 :=
  norm_eq_one_of_isUnitary (isUnitary_sgnL x (coefQ d σ) (lCell x hx l))
    (norm_stSel x hx d ψ hψ l σ)

/-- The letter prefix family of rung `l`: the first `m` controlled letters
applied to the mid-rung state. -/
noncomputable def ctrlPreQ (l : ℕ) (m : ℕ) (σ : STQc d) :
    HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  chainPre (List.finRange (2 ^ x))
    (fun s => regLift (ctrlReg x (lCell x hx l) s)
      ((pairGate (D := QubitCells (WL x)) (aC x (lCell x hx l)) (sC x s) Sum.inr_ne_inl
        (control (str x (lCell x hx l) s).gate)) :
        TSpace (QubitCells (WL x)) (ctrlReg x (lCell x hx l) s).toFun →ₗ[ℂ] _))
    m (sgnMidQ x hx d ψ l σ)

include hψ in
theorem norm_ctrlPreQ (l m : ℕ) (σ : STQc d) : ‖ctrlPreQ x hx d ψ l m σ‖ = 1 :=
  norm_eq_one_of_isUnitary
    (isUnitary_chainOp ((List.finRange (2 ^ x)).take m) _
      fun _ => isUnitary_regLift _ _)
    (norm_sgnMidQ x hx d ψ hψ l σ)

/-- The full letter prefix closes the rung: the inner loop exits at
`stSel (l + 1)`. -/
theorem ctrlPreQ_full (σ : STQc d) (l : ℕ) (hl : l < HubbardLCU.NT x) :
    ctrlPreQ x hx d ψ l (2 ^ x) σ = stSel x hx d ψ (l + 1) σ := by
  have hlen : (List.finRange (2 ^ x)).length = 2 ^ x := List.length_finRange
  have h := chainPre_length (List.finRange (2 ^ x))
    (fun s => regLift (ctrlReg x (lCell x hx l) s)
      ((pairGate (D := QubitCells (WL x)) (aC x (lCell x hx l)) (sC x s) Sum.inr_ne_inl
        (control (str x (lCell x hx l) s).gate)) :
        TSpace (QubitCells (WL x)) (ctrlReg x (lCell x hx l) s).toFun →ₗ[ℂ] _))
  rw [hlen] at h
  have hchain : ctrlPreQ x hx d ψ l (2 ^ x) σ
      = ctrlChain x (lCell x hx l) (sgnMidQ x hx d ψ l σ) := by
    rw [ctrlPreQ, h]
    rfl
  rw [hchain, sgnMidQ, lCell_eq_mk x hx hl, stSel, stSel,
    selPart_succ x (coefQ d σ) l hl, LinearMap.comp_apply, rungOp,
    LinearMap.comp_apply]

/-- One controlled-letter pass advances the prefix chain (concrete
registers). -/
theorem ctrlPreQ_step (σ : STQc d) (l m : ℕ) (hm : m < 2 ^ x) :
    regLift (ctrlReg x (lCell x hx l) (sCell x m))
        ((pairGate (D := QubitCells (WL x)) (aC x (lCell x hx l)) (sC x (sCell x m))
          Sum.inr_ne_inl (control (str x (lCell x hx l) (sCell x m)).gate)) :
          TSpace (QubitCells (WL x)) (ctrlReg x (lCell x hx l) (sCell x m)).toFun →ₗ[ℂ] _)
        (ctrlPreQ x hx d ψ l m σ)
      = ctrlPreQ x hx d ψ l (m + 1) σ := by
  rw [sCell_eq_mk x hm, ctrlPreQ, ctrlPreQ, chainPre_finRange_succ _ hm,
    LinearMap.comp_apply]

/-- The sign gate acts: rung `l` opens at the stored counter. -/
theorem sgnBodyQ_act (σ : STQc d) (l : ℕ) (hσ1 : σ.1.1 = l) :
    ∃ hinj : Function.Injective (sgnRegE x hx σ.1),
      regLift ⟨sgnRegE x hx σ.1, hinj⟩ (sgnGateE x hx σ.1)
        (stSel x hx d ψ l σ)
      = sgnMidQ x hx d ψ l σ := by
  subst hσ1
  exact ⟨(Reg.single (aC x (lCell x hx σ.1.1))).inj, rfl⟩

/-- The controlled letter acts, at the two stored counters. -/
theorem ctrlBodyQ_act (σ : STQc d) (l m : ℕ) (hσ1 : σ.1.1 = l)
    (hσ2 : σ.1.2.1 = m) (hm : m < 2 ^ x) :
    ∃ hinj : Function.Injective (ctrlRegE x hx σ.1),
      regLift ⟨ctrlRegE x hx σ.1, hinj⟩ (ctrlGateE x hx σ.1)
        (ctrlPreQ x hx d ψ l m σ)
      = ctrlPreQ x hx d ψ l (m + 1) σ := by
  subst hσ1
  subst hσ2
  exact ⟨(ctrlReg x (lCell x hx σ.1.1) (sCell x σ.1.2.1)).inj,
    ctrlPreQ_step x hx d ψ σ σ.1.1 σ.1.2.1 hm⟩

/-- The UNPREPARE prefix family: the first `k` inverse Givens gates (of the
reversed list) applied to the post-SELECT state. -/
noncomputable def unprepPreQ (k : ℕ) (σ : STQc d) :
    HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  chainPre ((List.finRange (HubbardLCU.NT x - 1)).reverse)
    (fun j => regLift (prepReg x j)
      ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
        (jA_ne_jB x j) (givens (-(ang x hx (coefQ d σ) (j : ℕ) (jA_lt x j))))) :
        TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _))
    k (stSel x hx d ψ (HubbardLCU.NT x) σ)

include hψ in
theorem norm_unprepPreQ (k : ℕ) (σ : STQc d) : ‖unprepPreQ x hx d ψ k σ‖ = 1 :=
  norm_eq_one_of_isUnitary
    (isUnitary_chainOp (((List.finRange (HubbardLCU.NT x - 1)).reverse).take k) _
      fun _ => isUnitary_regLift _ _)
    (norm_stSel x hx d ψ hψ (HubbardLCU.NT x) σ)

/-- The full UNPREPARE prefix is the whole inverse chain: the loop exits at
`st5`. -/
theorem unprepPreQ_full (σ : STQc d) :
    unprepPreQ x hx d ψ (HubbardLCU.NT x - 1) σ = st5 x hx d ψ σ := by
  have hlen : ((List.finRange (HubbardLCU.NT x - 1)).reverse).length
      = HubbardLCU.NT x - 1 := by
    rw [List.length_reverse, List.length_finRange]
  have h := chainPre_length ((List.finRange (HubbardLCU.NT x - 1)).reverse)
    (fun j => regLift (prepReg x j)
      ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
        (jA_ne_jB x j) (givens (-(ang x hx (coefQ d σ) (j : ℕ) (jA_lt x j))))) :
        TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _))
  rw [hlen] at h
  rw [unprepPreQ, h]
  rfl

/-- One UNPREPARE pass advances the prefix chain: the `k`-th gate of the
reversed list is the inverse Givens gate at position `N − 2 − k`. -/
theorem unprepPreQ_step (σ : STQc d) (k : ℕ) (hk : k < HubbardLCU.NT x - 1) :
    regLift (prepReg x (jCell x hx (HubbardLCU.NT x - 2 - k)))
        ((pairGate (D := QubitCells (WL x))
          (aC x (jA x (jCell x hx (HubbardLCU.NT x - 2 - k))))
          (aC x (jB x (jCell x hx (HubbardLCU.NT x - 2 - k))))
          (jA_ne_jB x (jCell x hx (HubbardLCU.NT x - 2 - k)))
          (givens (-(ang x hx (coefQ d σ)
            ((jCell x hx (HubbardLCU.NT x - 2 - k) : Fin (HubbardLCU.NT x - 1)) : ℕ)
            (jA_lt x (jCell x hx (HubbardLCU.NT x - 2 - k))))))) :
          TSpace (QubitCells (WL x))
            (prepReg x (jCell x hx (HubbardLCU.NT x - 2 - k))).toFun →ₗ[ℂ] _)
        (unprepPreQ x hx d ψ k σ)
      = unprepPreQ x hx d ψ (k + 1) σ := by
  have hlen : ((List.finRange (HubbardLCU.NT x - 1)).reverse).length
      = HubbardLCU.NT x - 1 := by
    rw [List.length_reverse, List.length_finRange]
  have hklen : k < ((List.finRange (HubbardLCU.NT x - 1)).reverse).length := by
    rw [hlen]
    exact hk
  have hj : HubbardLCU.NT x - 2 - k < HubbardLCU.NT x - 1 := by
    have := NT_gt_one x hx
    omega
  have hget : ((List.finRange (HubbardLCU.NT x - 1)).reverse).get ⟨k, hklen⟩
      = jCell x hx (HubbardLCU.NT x - 2 - k) := by
    rw [jCell_eq_mk x hx hj]
    refine Fin.ext ?_
    rw [List.get_eq_getElem, List.getElem_reverse, List.getElem_finRange]
    simp only [Fin.val_cast, List.length_finRange]
    omega
  rw [unprepPreQ, unprepPreQ, chainPre_succ _ _ hklen, hget, LinearMap.comp_apply]

/-- The UNPREPARE body acts, at the stored counter. -/
theorem unprepBodyQ_act (σ : STQc d) (k : ℕ) (hσ1 : σ.1.1 = k)
    (hk : k < HubbardLCU.NT x - 1) :
    ∃ hinj : Function.Injective (unprepRegE x hx σ.1),
      regLift ⟨unprepRegE x hx σ.1, hinj⟩ (unprepGateE x hx σ.1)
        (unprepPreQ x hx d ψ k σ)
      = unprepPreQ x hx d ψ (k + 1) σ := by
  subst hσ1
  exact ⟨(prepReg x (jCell x hx (HubbardLCU.NT x - 2 - σ.1.1))).inj,
    unprepPreQ_step x hx d ψ σ σ.1.1 hk⟩

/-! ## §7. The invariant, the rank, and the endpoint assertions -/

include hψ in
/-- The loop invariant: "`k ≤ d`, and the register is in the partial-product
state after `k` passes" — the state family at the raw counter, masked by the
counter bound (the counted-while mask pattern, `CountedWhile.inv`).  Inside
the body the guard gives `k < d`, so the mask is redundant there
(`startPremise`); at the exit the negated guard meets the mask at the single
point `k = d` (`post_le`). -/
noncomputable def J : Assn (STQc d) (QubitCells (WL x)) :=
  (Assn.ofStateFam (fun σ => st0 x hx d ψ σ) (norm_st0 x hx d ψ hψ)).mask
    fun σ => cnt d σ ≤ d

/-- The ranking function of (R-Loop-tot): the number of passes still to do. -/
def rank (σ : STQc d) : ℕ := d - cnt d σ

include hψ in
/-- The precondition `∣0⟩ₐ ⊗ ψ`. -/
noncomputable def Ppre : Assn (STQc d) (QubitCells (WL x)) :=
  Assn.ofStateFam (fun _ : STQc d => sysEmb x ψ) (fun _ => norm_inS x ψ hψ)

include hψ in
/-- The postcondition: the named output state — the full alternating product
after `d` passes, at the store's coefficients and angle array. -/
noncomputable def Qpost : Assn (STQc d) (QubitCells (WL x)) :=
  Assn.ofStateFam (fun σ : STQc d => qspSt x hx d ψ (coefQ d σ) (phis d σ) d)
    (fun σ => norm_qspSt x hx d ψ hψ (coefQ d σ) (phis d σ) d)

/-- On the mask (`k ≤ d`) the invariant reads the state-family projector. -/
theorem J_op_of_le (σ : STQc d) (h : cnt d σ ≤ d) :
    (J x hx d ψ hψ).op σ = outerLM (st0 x hx d ψ σ) (st0 x hx d ψ σ) :=
  Assn.mask_op_of_pos h

/-- Off the mask the invariant reads `0`. -/
theorem J_op_of_gt (σ : STQc d) (h : ¬ cnt d σ ≤ d) :
    (J x hx d ψ hψ).op σ = 0 :=
  Assn.mask_op_of_neg h

@[simp]
theorem Ppre_op (σ : STQc d) :
    (Ppre x d ψ hψ).op σ = outerLM (sysEmb x ψ) (sysEmb x ψ) := rfl

@[simp]
theorem Qpost_op (σ : STQc d) :
    (Qpost x hx d ψ hψ).op σ
      = outerLM (qspSt x hx d ψ (coefQ d σ) (phis d σ) d)
          (qspSt x hx d ψ (coefQ d σ) (phis d σ) d) := rfl

/-! ## §8. The loop-body derivation

The single gates (phase, the two `X` gates, the reflection) are one
(Ax-Uni)+(R-Conseq) each at the guard-masked family
(`DerivTot.unitary_stateFam_guard`); each counted fragment loop is ONE
`DerivTot.countedStateChain_rel` call along its §6b prefix family, the frame
predicate carrying the guard and the rank pin, bridged to the guard-masked
endpoints by the L-3 mask lemmas above. -/

/-- The phase gate: (Ax-Uni)+(R-Conseq) at the guard-masked family. -/
theorem phaseDeriv (p : ℕ → Prop) :
    DerivTot (((Assn.ofStateFam (fun σ : STQc d => st0 x hx d ψ σ)
        (norm_st0 x hx d ψ hψ)).mand (gdQ d)).mask fun σ : STQc d => p (cnt d σ))
      (phaseProg x hx d)
      (((Assn.ofStateFam (fun σ : STQc d => st1 x hx d ψ σ) (norm_st1 x hx d ψ hψ)).mand
        (gdQ d)).mask fun σ : STQc d => p (cnt d σ)) :=
  DerivTot.unitary_stateFam_guard (σT := STQc d) (L := WL x)
      (D := QubitCells (WL x)) (Reg.single (aC x (a0 x hx)))
    (fun σ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx))
      (phase (phiAt d σ)))
    (norm_st0 x hx d ψ hψ) (norm_st1 x hx d ψ hψ) (gdQ d)
    (fun σ : STQc d => p (cnt d σ)) (fun _ _ _ => rfl)

/-- The PREPARE fragment at the guard-masked family: the `X` gate one
(Ax-Uni)+(R-Conseq), the counted Givens loop one `countedStateChain_rel`
call along `prepPreQ`, glued by (R-Seq). -/
theorem prepQDeriv (p : ℕ → Prop) :
    DerivTot (((Assn.ofStateFam (fun σ : STQc d => st1 x hx d ψ σ) (norm_st1 x hx d ψ hψ)).mand
        (gdQ d)).mask fun σ : STQc d => p (cnt d σ))
      (prepQ x hx d)
      (((Assn.ofStateFam (fun σ : STQc d => st3 x hx d ψ σ) (norm_st3 x hx d ψ hψ)).mand
        (gdQ d)).mask fun σ : STQc d => p (cnt d σ)) := by
  rw [prepQ_eq]
  refine DerivTot.seq
    (DerivTot.unitary_stateFam_guard (σT := STQc d) (L := WL x)
      (D := QubitCells (WL x)) (Reg.single (aC x (a0 x hx)))
      (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)
      (norm_st1 x hx d ψ hψ) (norm_st2 x hx d ψ hψ) (gdQ d)
      (fun σ : STQc d => p (cnt d σ)) (fun _ _ _ => rfl)) ?_
  refine DerivTot.conseq
    (Assn.mand_mask_le (Assn.ofStateFam (fun σ : STQc d => st2 x hx d ψ σ) (norm_st2 x hx d ψ hψ))
      (gdQ d) (fun σ : STQc d => p (cnt d σ))) ?_
    (Assn.le_mand_mask (Assn.ofStateFam (fun σ : STQc d => st3 x hx d ψ σ) (norm_st3 x hx d ψ hψ))
      (gdQ d) (fun σ : STQc d => p (cnt d σ)))
  exact DerivTot.countedStateChain_relSource (cOuterQ d) (HubbardLCU.NT x - 1)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => prepPreQ x hx d ψ m σ)
    (fun m σ => norm_prepPreQ x hx d ψ hψ m σ)
    (fun _ _ _ => rfl)
    (fun _ _ => rfl)
    (fun (σ : STQc d) _ => prepPreQ_full x hx d ψ σ)
    (by
      rw [Assn.ofFam_ofStateFam, Assn.ofFam_ofStateFam]
      simp only [cOuterQ, cInnerQ, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst, Function.comp_apply,
        CounterLens.fst3, CounterLens.snd3]
      exact DerivTot.countedRung_fam (fun σ : STQc d => prepRegE x hx σ.1)
        (fun σ : STQc d => prepGateE x hx σ.1)
        (fun σ : STQc d => norm_prepPreQ x hx d ψ hψ σ.1.1 σ)
        (fun σ : STQc d => norm_prepPreQ x hx d ψ hψ (σ.1.1 + 1) σ)
        (fun (σ : STQc d) hσ => prepBodyQ_act x hx d ψ σ σ.1.1 rfl hσ.2))
    (fun _ => DerivTot.unitary_identity_mask (fun σ : STQc d => prepRegE x hx σ.1)
      (fun σ : STQc d => prepGateE x hx σ.1) (fun (σ : STQc d) _ => (prepReg x _).inj))

/-- The letter loop of rung `l`, relativised at the guard, the rank pin and
the outer counter pin: one `countedStateChain_rel` call along `ctrlPreQ`,
whose conclusion is exactly the shape the outer chain's step consumes. -/
theorem innerLoopQDeriv (p : ℕ → Prop) (l : ℕ) :
    DerivTot
      ((Assn.ofStateFam (fun σ : STQc d => sgnMidQ x hx d ψ l σ)
        (fun σ : STQc d => norm_sgnMidQ x hx d ψ hψ l σ)).mask
        fun σ : STQc d => (gdQ d σ = true ∧ p (cnt d σ))
          ∧ (cOuterQ d).get σ = l ∧ l < HubbardLCU.NT x)
      (countedProg (cInnerQ d) (fun _ => 2 ^ x)
        ((ctrlBody x hx).mapStore StoreLens.fst))
      ((Assn.ofStateFam (fun σ : STQc d => stSel x hx d ψ (l + 1) σ)
        (fun σ : STQc d => norm_stSel x hx d ψ hψ (l + 1) σ)).mask
        fun σ : STQc d => (gdQ d σ = true ∧ p (cnt d σ))
          ∧ (cOuterQ d).get σ = l ∧ l < HubbardLCU.NT x) :=
  DerivTot.countedStateChain_relSource (cInnerQ d) (2 ^ x)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => ctrlPreQ x hx d ψ l m σ)
    (fun m σ => norm_ctrlPreQ x hx d ψ hψ l m σ)
    (fun _ _ _ => rfl)
    (fun _ _ => rfl)
    (fun (σ : STQc d) hσ => ctrlPreQ_full x hx d ψ σ l hσ.2.2)
    (by
      rw [Assn.ofFam_ofStateFam, Assn.ofFam_ofStateFam]
      simp only [cOuterQ, cInnerQ, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst, Function.comp_apply,
        CounterLens.fst3, CounterLens.snd3]
      exact DerivTot.countedRung_fam (fun σ : STQc d => ctrlRegE x hx σ.1)
        (fun σ : STQc d => ctrlGateE x hx σ.1)
        (fun σ : STQc d => norm_ctrlPreQ x hx d ψ hψ l σ.1.2.1 σ)
        (fun σ : STQc d => norm_ctrlPreQ x hx d ψ hψ l (σ.1.2.1 + 1) σ)
        (fun (σ : STQc d) hσ => ctrlBodyQ_act x hx d ψ σ l σ.1.2.1 hσ.1.2.1 rfl hσ.2))
    (fun _ => DerivTot.unitary_identity_mask (fun σ : STQc d => ctrlRegE x hx σ.1)
      (fun σ : STQc d => ctrlGateE x hx σ.1) (fun (σ : STQc d) _ => (ctrlReg x _ _).inj))

/-- **One SELECT rung**, as the masked step obligation of the outer counted
loop: the sign rung (`countedRung_fam`) glued to the relativised letter loop
by (R-Seq). -/
theorem selStepQDeriv (p : ℕ → Prop) (l : ℕ) :
    DerivTot
      ((Assn.ofStateFam (fun σ : STQc d => stSel x hx d ψ l σ)
        (fun σ : STQc d => norm_stSel x hx d ψ hψ l σ)).mask
        fun σ : STQc d => (gdQ d σ = true ∧ p (cnt d σ))
          ∧ (cOuterQ d).get σ = l ∧ l < HubbardLCU.NT x)
      (((sgnBody x hx).mapStore StoreLens.fst).seq
        (countedProg (cInnerQ d) (fun _ => 2 ^ x)
          ((ctrlBody x hx).mapStore StoreLens.fst)))
      ((Assn.ofStateFam (fun σ : STQc d => stSel x hx d ψ (l + 1) σ)
        (fun σ : STQc d => norm_stSel x hx d ψ hψ (l + 1) σ)).mask
        fun σ : STQc d => (gdQ d σ = true ∧ p (cnt d σ))
          ∧ (cOuterQ d).get σ = l ∧ l < HubbardLCU.NT x) :=
  DerivTot.seq
    (DerivTot.countedRung_fam (fun σ : STQc d => sgnRegE x hx σ.1)
      (fun σ : STQc d => sgnGateE x hx σ.1)
      (fun σ : STQc d => norm_stSel x hx d ψ hψ l σ)
      (fun σ : STQc d => norm_sgnMidQ x hx d ψ hψ l σ)
      (fun (σ : STQc d) hσ => sgnBodyQ_act x hx d ψ σ l hσ.2.1))
    (innerLoopQDeriv x hx d ψ hψ p l)

/-- The mapped SELECT rung preserves any predicate insensitive to inner-counter writes. -/
theorem rungIdentityQ (φ : STQc d → Prop)
    (hφ : ∀ σ v, φ ((cInnerQ d).set σ v) ↔ φ σ) :
    DerivTot ((Assn.one : Assn (STQc d) (QubitCells (WL x))).mask φ)
      (((sgnBody x hx).mapStore StoreLens.fst).seq
        (countedProg (cInnerQ d) (fun _ => 2 ^ x)
          ((ctrlBody x hx).mapStore StoreLens.fst))) (Assn.one.mask φ) :=
  DerivTot.seq
    (DerivTot.unitary_identity_mask (fun σ : STQc d => sgnRegE x hx σ.1)
      (fun σ : STQc d => sgnGateE x hx σ.1) (fun (σ : STQc d) _ => (Reg.single _).inj))
    (DerivTot.countedIdentitySource (cInnerQ d) hφ (fun _ _ => rfl)
      (DerivTot.unitary_identity_mask (fun σ : STQc d => ctrlRegE x hx σ.1)
        (fun σ : STQc d => ctrlGateE x hx σ.1) (fun (σ : STQc d) _ => (ctrlReg x _ _).inj))
      (fun _ => DerivTot.unitary_identity_mask (fun σ : STQc d => ctrlRegE x hx σ.1)
        (fun σ : STQc d => ctrlGateE x hx σ.1) (fun (σ : STQc d) _ => (ctrlReg x _ _).inj)))

/-- SELECT invariant preservation at the current outer counter. -/
theorem selStepQSource (p : ℕ → Prop) :
    DerivTot
      ((Assn.ofStateFam (fun σ : STQc d => stSel x hx d ψ σ.1.1 σ)
        (fun σ : STQc d => norm_stSel x hx d ψ hψ σ.1.1 σ)).mask
        fun σ : STQc d => (gdQ d σ = true ∧ p (cnt d σ)) ∧ σ.1.1 < HubbardLCU.NT x)
      (((sgnBody x hx).mapStore StoreLens.fst).seq
        (countedProg (cInnerQ d) (fun _ => 2 ^ x)
          ((ctrlBody x hx).mapStore StoreLens.fst)))
      ((Assn.ofStateFam (fun σ : STQc d => stSel x hx d ψ (σ.1.1 + 1) σ)
        (fun σ : STQc d => norm_stSel x hx d ψ hψ (σ.1.1 + 1) σ)).mask
        fun σ : STQc d => (gdQ d σ = true ∧ p (cnt d σ)) ∧ σ.1.1 < HubbardLCU.NT x) := by
  refine DerivTot.seq
    (DerivTot.countedRung_fam (fun σ : STQc d => sgnRegE x hx σ.1)
      (fun σ : STQc d => sgnGateE x hx σ.1)
      (fun σ : STQc d => norm_stSel x hx d ψ hψ σ.1.1 σ)
      (fun σ : STQc d => norm_sgnMidQ x hx d ψ hψ σ.1.1 σ)
      (fun (σ : STQc d) _ => sgnBodyQ_act x hx d ψ σ σ.1.1 rfl)) ?_
  exact DerivTot.countedStateChain_relSource (cInnerQ d) (2 ^ x)
    (φ := fun σ => (gdQ d σ = true ∧ p (cnt d σ)) ∧ σ.1.1 < HubbardLCU.NT x)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => ctrlPreQ x hx d ψ σ.1.1 m σ)
    (fun m σ => norm_ctrlPreQ x hx d ψ hψ σ.1.1 m σ)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun (σ : STQc d) hσ => ctrlPreQ_full x hx d ψ σ σ.1.1 hσ.2)
    (by
      rw [Assn.ofFam_ofStateFam, Assn.ofFam_ofStateFam]
      simp only [cOuterQ, cInnerQ, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst, Function.comp_apply,
        CounterLens.fst3, CounterLens.snd3]
      exact DerivTot.countedRung_fam (fun σ : STQc d => ctrlRegE x hx σ.1)
        (fun σ : STQc d => ctrlGateE x hx σ.1)
        (fun σ : STQc d => norm_ctrlPreQ x hx d ψ hψ σ.1.1 σ.1.2.1 σ)
        (fun σ : STQc d => norm_ctrlPreQ x hx d ψ hψ σ.1.1 (σ.1.2.1 + 1) σ)
        (fun (σ : STQc d) hσ => ctrlBodyQ_act x hx d ψ σ σ.1.1 σ.1.2.1 rfl rfl hσ.2))
    (fun _ => DerivTot.unitary_identity_mask (fun σ : STQc d => ctrlRegE x hx σ.1)
      (fun σ : STQc d => ctrlGateE x hx σ.1) (fun (σ : STQc d) _ => (ctrlReg x _ _).inj))

/-- The SELECT fragment: the counted rung loop in one `countedStateChain_rel`
call along `stSel`, its step the (R-Seq) glue of the sign rung and the
relativised letter loop. -/
theorem selQDeriv (p : ℕ → Prop) :
    DerivTot (((Assn.ofStateFam (fun σ : STQc d => st3 x hx d ψ σ) (norm_st3 x hx d ψ hψ)).mand
        (gdQ d)).mask fun σ : STQc d => p (cnt d σ))
      (selQ x hx d)
      (((Assn.ofStateFam (fun σ : STQc d => stSel x hx d ψ (HubbardLCU.NT x) σ)
        (norm_stSel x hx d ψ hψ (HubbardLCU.NT x))).mand (gdQ d)).mask
        fun σ : STQc d => p (cnt d σ)) := by
  rw [selQ_eq]
  refine DerivTot.conseq
    (Assn.mand_mask_le (Assn.ofStateFam (fun σ : STQc d => st3 x hx d ψ σ) (norm_st3 x hx d ψ hψ))
      (gdQ d) (fun σ : STQc d => p (cnt d σ))) ?_
    (Assn.le_mand_mask (Assn.ofStateFam (fun σ : STQc d => stSel x hx d ψ (HubbardLCU.NT x) σ)
      (norm_stSel x hx d ψ hψ (HubbardLCU.NT x))) (gdQ d) (fun σ : STQc d => p (cnt d σ)))
  exact DerivTot.countedStateChain_relSource (cOuterQ d) (HubbardLCU.NT x)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun l σ => stSel x hx d ψ l σ)
    (fun l σ => norm_stSel x hx d ψ hψ l σ)
    (fun _ _ _ => rfl)
    (fun (σ : STQc d) _ => by
      rw [stSel, show selPart x (coefQ d σ) 0 = 1 from rfl, Module.End.one_apply])
    (fun _ _ => rfl)
    (by simpa only [Assn.ofFam_ofStateFam, cOuterQ, CounterLens.pullbackFst,
          CounterLens.pullback, StoreLens.fst, Function.comp_apply, CounterLens.fst3]
          using selStepQSource x hx d ψ hψ p)
    (fun _ => rungIdentityQ x hx d _ (fun _ _ => Iff.rfl))

/-- The UNPREPARE fragment at the guard-masked family: the counted inverse
Givens loop one `countedStateChain_rel` call along `unprepPreQ`, then the `X`
gate, glued by (R-Seq). -/
theorem unprepQDeriv (p : ℕ → Prop) :
    DerivTot (((Assn.ofStateFam (fun σ : STQc d => stSel x hx d ψ (HubbardLCU.NT x) σ)
        (norm_stSel x hx d ψ hψ (HubbardLCU.NT x))).mand (gdQ d)).mask
        fun σ : STQc d => p (cnt d σ))
      (unprepQ x hx d)
      (((Assn.ofStateFam (fun σ : STQc d => st6 x hx d ψ σ) (norm_st6 x hx d ψ hψ)).mand
        (gdQ d)).mask fun σ : STQc d => p (cnt d σ)) := by
  rw [unprepQ_eq]
  refine DerivTot.seq ?_
    (DerivTot.unitary_stateFam_guard (σT := STQc d) (L := WL x)
      (D := QubitCells (WL x)) (Reg.single (aC x (a0 x hx)))
      (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)
      (norm_st5 x hx d ψ hψ) (norm_st6 x hx d ψ hψ) (gdQ d)
      (fun σ : STQc d => p (cnt d σ)) (fun _ _ _ => rfl))
  refine DerivTot.conseq
    (Assn.mand_mask_le (Assn.ofStateFam (fun σ : STQc d => stSel x hx d ψ (HubbardLCU.NT x) σ)
      (norm_stSel x hx d ψ hψ (HubbardLCU.NT x))) (gdQ d) (fun σ : STQc d => p (cnt d σ))) ?_
    (Assn.le_mand_mask (Assn.ofStateFam (fun σ : STQc d => st5 x hx d ψ σ) (norm_st5 x hx d ψ hψ))
      (gdQ d) (fun σ : STQc d => p (cnt d σ)))
  exact DerivTot.countedStateChain_relSource (cOuterQ d) (HubbardLCU.NT x - 1)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k σ => unprepPreQ x hx d ψ k σ)
    (fun k σ => norm_unprepPreQ x hx d ψ hψ k σ)
    (fun _ _ _ => rfl)
    (fun _ _ => rfl)
    (fun (σ : STQc d) _ => unprepPreQ_full x hx d ψ σ)
    (by
      rw [Assn.ofFam_ofStateFam, Assn.ofFam_ofStateFam]
      simp only [cOuterQ, cInnerQ, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst, Function.comp_apply,
        CounterLens.fst3, CounterLens.snd3]
      exact DerivTot.countedRung_fam (fun σ : STQc d => unprepRegE x hx σ.1)
        (fun σ : STQc d => unprepGateE x hx σ.1)
        (fun σ : STQc d => norm_unprepPreQ x hx d ψ hψ σ.1.1 σ)
        (fun σ : STQc d => norm_unprepPreQ x hx d ψ hψ (σ.1.1 + 1) σ)
        (fun (σ : STQc d) hσ => unprepBodyQ_act x hx d ψ σ σ.1.1 rfl hσ.2))
    (fun _ => DerivTot.unitary_identity_mask (fun σ : STQc d => unprepRegE x hx σ.1)
      (fun σ : STQc d => unprepGateE x hx σ.1) (fun (σ : STQc d) _ => (prepReg x _).inj))

/-- The reflection at the guard-masked family. -/
theorem reflDeriv (p : ℕ → Prop) :
    DerivTot (((Assn.ofStateFam (fun σ : STQc d => st6 x hx d ψ σ) (norm_st6 x hx d ψ hψ)).mand
        (gdQ d)).mask fun σ : STQc d => p (cnt d σ))
      (reflProg x hx d)
      (((Assn.ofStateFam (fun σ : STQc d => st7 x hx d ψ σ) (norm_st7 x hx d ψ hψ)).mand
        (gdQ d)).mask fun σ : STQc d => p (cnt d σ)) :=
  DerivTot.unitary_stateFam_guard (σT := STQc d) (L := WL x)
      (D := QubitCells (WL x)) (Reg.single (aC x (a0 x hx)))
    (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) Z)
    (norm_st6 x hx d ψ hψ) (norm_st7 x hx d ψ hψ) (gdQ d)
    (fun σ : STQc d => p (cnt d σ)) (fun _ _ _ => rfl)

/-- **The pass closes**: the state after the phase gate, the LCU fragments
and the reflection is the next partial-product state — the alternating
product advanced by one factor.  At the raw counter this is unconditional:
no saturation arithmetic. -/
theorem st7_eq (σ : STQc d) :
    st7 x hx d ψ σ = qspSt x hx d ψ (coefQ d σ) (phis d σ) (cnt d σ + 1) := by
  rw [qspSt, Qubitization.qspIter_succ]
  rw [st7, st6, st5, stSel, st3, st2, st1, st0]
  rfl

/-- The pass exit entails the next invariant under the incremented counter:
the (R-Conseq) premise feeding (Ax-Ass), with the rank strictly decreased. -/
theorem endPremise (r₀ : ℕ) :
    (((Assn.ofStateFam (fun σ => st7 x hx d ψ σ) (norm_st7 x hx d ψ hψ)).mand
        (gdQ d)).mask fun σ => rank d σ = r₀)
      ≤ ((J x hx d ψ hψ).mask fun σ => rank d σ < r₀).comp
          fun σ : STQc d => (σ.1, σ.2.1, σ.2.2 + 1) := by
  intro σ
  by_cases hm : rank d σ = r₀
  · by_cases hg : gdQ d σ = true
    · have hlt : cnt d σ < d := by simpa [gdQ] using hg
      have hrk : rank d (σ.1, σ.2.1, σ.2.2 + 1) < r₀ := by
        simp only [rank, cnt] at hm hlt ⊢
        omega
      have hle : cnt d ((σ.1, σ.2.1, σ.2.2 + 1) : STQc d) ≤ d := by
        simp only [cnt] at hlt ⊢
        omega
      refine le_of_eq ?_
      rw [Assn.mask_op_of_pos
          (A := (Assn.ofStateFam (fun σ => st7 x hx d ψ σ) (norm_st7 x hx d ψ hψ)).mand
            (gdQ d)) hm,
        Assn.mand_op_of_true
          (A := Assn.ofStateFam (fun σ => st7 x hx d ψ σ) (norm_st7 x hx d ψ hψ)) hg,
        Assn.comp_op,
        Assn.mask_op_of_pos (A := J x hx d ψ hψ) hrk,
        Assn.ofStateFam_op,
        J_op_of_le x hx d ψ hψ (σ.1, σ.2.1, σ.2.2 + 1) hle]
      rw [st7_eq x hx d ψ σ]
      rfl
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos
        (A := (Assn.ofStateFam (fun σ => st7 x hx d ψ σ) (norm_st7 x hx d ψ hψ)).mand
          (gdQ d)) hm]
      exact Assn.mand_op_of_false
        (A := Assn.ofStateFam (fun σ => st7 x hx d ψ σ) (norm_st7 x hx d ψ hψ))
        (by simpa using hg)
  · exact Assn.op_zero_le (Assn.mask_op_of_neg
      (A := (Assn.ofStateFam (fun σ => st7 x hx d ψ σ) (norm_st7 x hx d ψ hψ)).mand
        (gdQ d)) hm)

/-- The loop entry: under the guard the counter-bound mask of the invariant
is redundant (`k < d` gives `k ≤ d`), so the masked invariant entails the raw
state family the pass derivation starts from — the (R-Conseq) premise opening
the body. -/
theorem startPremise (r₀ : ℕ) :
    (((J x hx d ψ hψ).mand (gdQ d)).mask fun σ => rank d σ = r₀)
      ≤ (((Assn.ofStateFam (fun σ => st0 x hx d ψ σ)
          (norm_st0 x hx d ψ hψ)).mand (gdQ d)).mask fun σ => rank d σ = r₀) := by
  intro σ
  by_cases hm : rank d σ = r₀
  · by_cases hg : gdQ d σ = true
    · have hle : cnt d σ ≤ d := le_of_lt (by simpa [gdQ] using hg)
      refine le_of_eq ?_
      rw [Assn.mask_op_of_pos (A := (J x hx d ψ hψ).mand (gdQ d)) hm,
        Assn.mask_op_of_pos
          (A := (Assn.ofStateFam (fun σ => st0 x hx d ψ σ)
            (norm_st0 x hx d ψ hψ)).mand (gdQ d)) hm,
        Assn.mand_op_of_true (A := J x hx d ψ hψ) hg,
        Assn.mand_op_of_true
          (A := Assn.ofStateFam (fun σ => st0 x hx d ψ σ)
            (norm_st0 x hx d ψ hψ)) hg,
        J_op_of_le x hx d ψ hψ σ hle, Assn.ofStateFam_op]
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := (J x hx d ψ hψ).mand (gdQ d)) hm]
      exact Assn.mand_op_of_false (A := J x hx d ψ hψ) (by simpa using hg)
  · exact Assn.op_zero_le
      (Assn.mask_op_of_neg (A := (J x hx d ψ hψ).mand (gdQ d)) hm)

/-- The loop body at rank value `r₀`: the entry entailment drops the redundant
counter-bound mask (`startPremise`), the phase gate, the three fragments and
the reflection chained by (R-Seq), closed by (Ax-Ass) on `k := k + 1`. -/
theorem bodyDeriv (r₀ : ℕ) :
    DerivTot (((J x hx d ψ hψ).mand (gdQ d)).mask fun σ => rank d σ = r₀)
      (bodyProg x hx d)
      ((J x hx d ψ hψ).mask fun σ => rank d σ < r₀) := by
  refine DerivTot.seq (DerivTot.conseq (startPremise x hx d ψ hψ r₀) ?_
    (endPremise x hx d ψ hψ r₀))
    (DerivTot.assign _ ((J x hx d ψ hψ).mask fun σ => rank d σ < r₀))
  refine DerivTot.seq (phaseDeriv x hx d ψ hψ (fun k => d - k = r₀)) ?_
  refine DerivTot.seq (prepQDeriv x hx d ψ hψ (fun k => d - k = r₀)) ?_
  refine DerivTot.seq (selQDeriv x hx d ψ hψ (fun k => d - k = r₀)) ?_
  exact DerivTot.seq (unprepQDeriv x hx d ψ hψ (fun k => d - k = r₀))
    (reflDeriv x hx d ψ hψ (fun k => d - k = r₀))

/-- Every circuit fragment preserves a predicate on the QSP counter on all
quantum inputs. The internal counted loops use the source rule. -/
theorem passIdentity (p : ℕ → Prop) :
    DerivTot ((Assn.one : Assn (STQc d) (QubitCells (WL x))).mask fun σ : STQc d => p (cnt d σ))
      ((phaseProg x hx d).seq (wPassProg x hx d))
      (Assn.one.mask fun σ : STQc d => p (cnt d σ)) := by
  refine DerivTot.seq
    (DerivTot.unitary_identity_mask _ _ (fun _ _ => (Reg.single _).inj)) ?_
  let A : Assn (STQc d) (QubitCells (WL x)) := Assn.one.mask fun σ : STQc d => p (cnt d σ)
  refine DerivTot.seq (B := A) ?_
    (DerivTot.seq (B := A) ?_ (DerivTot.seq (B := A) ?_ ?_))
  · rw [prepQ_eq]
    refine DerivTot.seq
      (DerivTot.unitary_identity_mask _ _ (fun _ _ => (Reg.single _).inj)) ?_
    exact DerivTot.countedIdentitySource (cOuterQ d) (fun _ _ => Iff.rfl)
      (fun _ _ => rfl)
      (DerivTot.unitary_identity_mask (fun σ : STQc d => prepRegE x hx σ.1)
        (fun σ : STQc d => prepGateE x hx σ.1) (fun (σ : STQc d) _ => (prepReg x _).inj))
      (fun _ => DerivTot.unitary_identity_mask (fun σ : STQc d => prepRegE x hx σ.1)
        (fun σ : STQc d => prepGateE x hx σ.1) (fun (σ : STQc d) _ => (prepReg x _).inj))
  · rw [selQ_eq]
    exact DerivTot.countedIdentitySource (cOuterQ d) (fun _ _ => Iff.rfl)
      (fun _ _ => rfl)
      (rungIdentityQ x hx d _ (fun _ _ => Iff.rfl))
      (fun _ => rungIdentityQ x hx d _ (fun _ _ => Iff.rfl))
  · rw [unprepQ_eq]
    refine DerivTot.seq ?_
      (DerivTot.unitary_identity_mask _ _ (fun _ _ => (Reg.single _).inj))
    exact DerivTot.countedIdentitySource (cOuterQ d) (fun _ _ => Iff.rfl)
      (fun _ _ => rfl)
      (DerivTot.unitary_identity_mask (fun σ : STQc d => unprepRegE x hx σ.1)
        (fun σ : STQc d => unprepGateE x hx σ.1) (fun (σ : STQc d) _ => (prepReg x _).inj))
      (fun _ => DerivTot.unitary_identity_mask (fun σ : STQc d => unprepRegE x hx σ.1)
        (fun σ : STQc d => unprepGateE x hx σ.1) (fun (σ : STQc d) _ => (prepReg x _).inj))
  · exact DerivTot.unitary_identity_mask _ _ (fun _ _ => (Reg.single _).inj)

/-- The source rule's unranked invariant-preservation premise. -/
theorem bodyInvariantDeriv :
    DerivTot ((J x hx d ψ hψ).mand (gdQ d)) (bodyProg x hx d) (J x hx d ψ hψ) := by
  have ht (A : Assn (STQc d) (QubitCells (WL x))) : A.mask (fun _ => True) = A := by
    ext σ; simp
  have hp := DerivTot.seq (phaseDeriv x hx d ψ hψ (fun _ => True))
    (DerivTot.seq (prepQDeriv x hx d ψ hψ (fun _ => True))
      (DerivTot.seq (selQDeriv x hx d ψ hψ (fun _ => True))
        (DerivTot.seq (unprepQDeriv x hx d ψ hψ (fun _ => True))
          (reflDeriv x hx d ψ hψ (fun _ => True)))))
  simp only [ht] at hp
  refine DerivTot.seq (DerivTot.conseq ?_ hp ?_)
    (DerivTot.assign (fun σ : STQc d => (σ.1, σ.2.1, σ.2.2 + 1)) (J x hx d ψ hψ))
  · intro σ
    by_cases hg : gdQ d σ = true
    · rw [Assn.mand_op_of_true hg, Assn.mand_op_of_true hg,
        J_op_of_le x hx d ψ hψ σ (le_of_lt (by simpa [gdQ] using hg)),
        Assn.ofStateFam_op]
    · exact Assn.op_zero_le (Assn.mand_op_of_false (by simpa using hg))
  · intro σ
    by_cases hg : gdQ d σ = true
    · have hlt : cnt d σ < d := by simpa [gdQ] using hg
      have hle : cnt d ((σ.1, σ.2.1, σ.2.2 + 1) : STQc d) ≤ d := by
        simp only [cnt] at hlt ⊢; omega
      refine le_of_eq ?_
      rw [Assn.mand_op_of_true hg, Assn.comp_op,
        J_op_of_le x hx d ψ hψ (σ.1, σ.2.1, σ.2.2 + 1) hle, Assn.ofStateFam_op]
      rw [st7_eq x hx d ψ σ]
      rfl
    · exact Assn.op_zero_le (Assn.mand_op_of_false (by simpa using hg))

/-- Identity-predicate decrease is proved independently of the state invariant. -/
theorem bodyIdentityRankDeriv (z : Int) :
    DerivTot ((Assn.one : Assn (STQc d) (QubitCells (WL x))).mask fun σ =>
      cnt d σ ≤ d ∧ gdQ d σ = true ∧ (rank d σ : Int) = z)
      (bodyProg x hx d) (Assn.one.mask fun σ => (rank d σ : Int) < z) := by
  refine DerivTot.seq (DerivTot.conseq ?_
    (passIdentity x hx d (fun k => k ≤ d ∧ decide (k < d) = true ∧ ((d-k : ℕ) : Int) = z))
    ?_) (DerivTot.assign _ _)
  · exact Assn.le_refl' _
  · apply Assn.mask_le_of_imp_le
    intro σ hσ
    have hlt : cnt d σ < d := by simpa using hσ.2.1
    rw [Assn.comp_op, Assn.mask_op_of_pos (by
      simp only [rank, cnt] at hσ hlt ⊢
      omega)]
    exact le_rfl

/-! ## §9. The loop, the triple, and soundness -/

/-- **(R-Loop-tot)**: the invariant with ranking function `rank k = d − k` —
DEFINITE termination, no meta-level rule. -/
theorem loopDeriv :
    DerivTot (J x hx d ψ hψ) (Prog.while (gdQ d) (bodyProg x hx d))
      ((J x hx d ψ hψ).mandNot (gdQ d)) :=
  DerivTot.whileLoopSource (A := Assn.ofStateFam (fun σ => st0 x hx d ψ σ)
    (norm_st0 x hx d ψ hψ)) (φ := fun σ => cnt d σ ≤ d)
    (fun σ => (rank d σ : Int)) (fun _ _ => Int.natCast_nonneg _)
    (bodyInvariantDeriv x hx d ψ hψ) (bodyIdentityRankDeriv x hx d)

theorem pre_le :
    Ppre x d ψ hψ
      ≤ (J x hx d ψ hψ).comp fun σ : STQc d => (σ.1, σ.2.1, 0) := by
  intro σ
  refine le_of_eq ?_
  rw [Ppre_op, Assn.comp_op,
    J_op_of_le x hx d ψ hψ (σ.1, σ.2.1, 0) (Nat.zero_le d)]
  rfl

/-- The exit entailment reads the `k = d` point: the negated guard gives
`d ≤ k`, the invariant's mask gives `k ≤ d`, and off the mask the invariant
reads `0`. -/
theorem post_le :
    (J x hx d ψ hψ).mandNot (gdQ d) ≤ Qpost x hx d ψ hψ := by
  intro σ
  by_cases hg : gdQ d σ = true
  · exact Assn.op_zero_le
      (Assn.mandNot_op_of_true (A := J x hx d ψ hψ) hg)
  · have hσ : d ≤ cnt d σ := by simpa [gdQ] using hg
    by_cases hle : cnt d σ ≤ d
    · have hcnt : cnt d σ = d := le_antisymm hle hσ
      refine le_of_eq ?_
      rw [Assn.mandNot_op_of_false (A := J x hx d ψ hψ) (by simpa using hg),
        J_op_of_le x hx d ψ hψ σ hle, Qpost_op, st0, hcnt]
    · refine Assn.op_zero_le ?_
      rw [Assn.mandNot_op_of_false (A := J x hx d ψ hψ) (by simpa using hg)]
      exact J_op_of_gt x hx d ψ hψ σ hle

/-- **Tier 1, the derivation**: the exact evolution triple of the QSP loop —
`{ ∣0⟩ₐ ⊗ ψ } qspProg { ∣Ξ_out⟩ }`, the named output the alternating product
`∏_{k<d} (refl ∘ lcu ∘ phase(φ k))` applied to the input, derived in
`QHL⁺_tot` with the ranked (R-Loop-tot). -/
theorem qspDeriv :
    DerivTot (Ppre x d ψ hψ) (qspProg x hx d) (Qpost x hx d ψ hψ) :=
  DerivTot.conseq (pre_le x hx d ψ hψ)
    (DerivTot.seq (DerivTot.assign _ (J x hx d ψ hψ)) (loopDeriv x hx d ψ hψ))
    (post_le x hx d ψ hψ)

/-- **Tier 1, soundness**: the semantic total-correctness statement. -/
theorem qspValid :
    validTot (Ppre x d ψ hψ) (qspProg x hx d) (Qpost x hx d ψ hψ) :=
  (qspDeriv x hx d ψ hψ).sound

/-! ## §10. Non-vacuity -/

include hψ in
/-- The precondition holds with expectation `1` on the concrete pure input
`∣0⟩ₐ ⊗ ψ`, at any store value: the triple is not vacuous. -/
theorem qspPre_expect_one (σ₀ : STQc d) :
    expectE (Ppre x d ψ hψ).op ⟨σ₀, PDensity.pure (sysEmb x ψ)⟩ = 1 := by
  rw [expectE_pure, Ppre_op, outerLM_apply]
  have hvv : (⟪sysEmb x ψ, sysEmb x ψ⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ),
      show ‖sysEmb x ψ‖ = 1 from norm_inS x ψ hψ]
    norm_num
  rw [inner_smul_right, hvv]
  simp

/-! ## §11. The LCU pass on embedded states (Tier 2 groundwork)

The semantic operators of §4 evaluated on the block: the pass carries
`∣0⟩ₐ ⊗ w` to the lane-(iii) output state `outSt`, and squares to the
identity on the block (`select` squares to the identity on the one-hot
sector because the signs and the Pauli strings are involutions). -/

theorem xLift_invol (z : HS (QubitCells (WL x)) (univ : Finset (WL x))) :
    xLift x hx (xLift x hx z) = z := by
  have h := LinearMap.ext_iff.mp (xLift_comp_self x hx) z
  simpa using h

theorem prepChain_eq_adj (τ : ST) :
    prepChain x hx τ = LinearMap.adjoint (unprepChain x hx τ) :=
  (adjoint_unprepChain x hx τ).symm

theorem prepChain_unprepChain (τ : ST) (z : HS (QubitCells (WL x)) (univ : Finset (WL x))) :
    prepChain x hx τ (unprepChain x hx τ z) = z := by
  rw [prepChain_eq_adj]
  have h := LinearMap.ext_iff.mp (isUnitary_unprepChain x hx τ).1 z
  simpa using h

theorem unprepChain_prepChain (τ : ST) (z : HS (QubitCells (WL x)) (univ : Finset (WL x))) :
    unprepChain x hx τ (prepChain x hx τ z) = z := by
  rw [prepChain_eq_adj]
  have h := LinearMap.ext_iff.mp (isUnitary_unprepChain x hx τ).2 z
  simpa using h

theorem xLift_sysEmb (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    xLift x hx (sysEmb x w) = ancEmbed (L₁ := SysL x) (oneHot x (a0 x hx)) w :=
  xGate_emb x hx w

theorem xLift_oneHot_emb (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    xLift x hx (ancEmbed (L₁ := SysL x) (oneHot x (a0 x hx)) w) = sysEmb x w := by
  rw [← xLift_sysEmb x hx w, xLift_invol]

theorem prepChain_emb (τ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    prepChain x hx τ (ancEmbed (L₁ := SysL x) (oneHot x (a0 x hx)) w)
      = fullSt x hx w τ := by
  have h := prep_chain x hx τ w
  rw [prepSt_zero x hx w τ, prepSt_full x hx w τ] at h
  exact h

theorem rungOp_selSt (τ : ST) (l : AncL x)
    (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    rungOp x τ l (selSt x hx w τ (l : ℕ)) = selSt x hx w τ ((l : ℕ) + 1) := by
  show ctrlChain x l (sgnL x τ l (selSt x hx w τ (l : ℕ))) = _
  rw [show sgnL x τ l (selSt x hx w τ (l : ℕ)) = selMid x hx w τ l 0 from
      sgn_step x hx τ l w,
    show ctrlChain x l (selMid x hx w τ l 0) = selMid x hx w τ l (2 ^ x) from
      rung_chain x hx τ l w]
  exact selMid_top x hx τ l w

theorem selPart_fullSt (τ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))
    (l : ℕ) (hl : l ≤ HubbardLCU.NT x) :
    selPart x τ l (fullSt x hx w τ) = selSt x hx w τ l := by
  induction l with
  | zero =>
      rw [show selPart x τ 0 = 1 from rfl, Module.End.one_apply]
      exact (selSt_zero x hx w τ).symm
  | succ l ih =>
      have hl' : l < HubbardLCU.NT x := by omega
      rw [selPart_succ x τ l hl', LinearMap.comp_apply, ih (by omega)]
      exact rungOp_selSt x hx τ ⟨l, hl'⟩ w

theorem selOp_fullSt (τ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    selOp x τ (fullSt x hx w τ) = selSt x hx w τ (HubbardLCU.NT x) :=
  selPart_fullSt x hx τ w _ le_rfl

/-- **The pass on the block**: the LCU pass carries `∣0⟩ₐ ⊗ w` to the
lane-(iii) output state. -/
theorem lcuOp_emb (τ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    lcuOp x hx τ (sysEmb x w) = outSt x hx w τ := by
  show xLift x hx (unprepChain x hx τ (selOp x τ (prepChain x hx τ
    (xLift x hx (sysEmb x w))))) = _
  rw [xLift_sysEmb, prepChain_emb, selOp_fullSt]
  rfl

/-! ## §12. The one-hot sector: generic branch families -/

/-- A one-hot superposition with an arbitrary system vector per branch. -/
noncomputable def ohSum (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  ∑ i : AncL x, ancEmbed (L₁ := SysL x) (oneHot x i) (u i)

theorem selSt_eq_ohSum (τ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))
    (l : ℕ) :
    selSt x hx w τ l
      = ohSum x (fun i => ((am x hx τ i : ℝ) : ℂ) • selW x τ l i w) := by
  rw [selSt, ohSum]
  exact Finset.sum_congr rfl fun i _ => (map_smul _ _ _).symm

theorem fullSt_eq_ohSum (τ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    fullSt x hx w τ = ohSum x (fun i => ((am x hx τ i : ℝ) : ℂ) • w) := by
  rw [fullSt, ohSum]
  exact Finset.sum_congr rfl fun i _ => (map_smul _ _ _).symm

/-- The sign gate on a generic branch family: branch `l` acquires the sign. -/
theorem sgnL_ohSum (τ : ST) (l : AncL x)
    (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    sgnL x τ l (ohSum x u)
      = ohSum x (Function.update u l (((sg x τ l : ℝ) : ℂ) • u l)) := by
  rw [ohSum, ohSum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hU : (sgnGate (cf x τ l) : 𝕢 →ₗ[ℂ] 𝕢)
      (EuclideanSpace.single (oneHot x i l) 1)
      = (if oneHot x i l then (if cf x τ l < 0 then (-1 : ℂ) else 1) else 1) •
          EuclideanSpace.single (oneHot x i l) 1 := sgnGate_single _ _
  have h := gateAt_inr_ancEmbed (L₁ := SysL x) l (sgnGate (cf x τ l)) (oneHot x i) hU (u i)
  rw [Function.update_eq_self] at h
  refine h.trans ?_
  by_cases hil : i = l
  · subst hil
    rw [Function.update_self, oneHot_self, if_pos rfl, map_smul]
    congr 1
    rw [sg]
    split_ifs <;> norm_num
  · rw [Function.update_of_ne hil, oneHot_ne x (Ne.symm hil),
      if_neg Bool.false_ne_true, one_smul]

/-- Every controlled letter fixes a branch whose flag is elsewhere. -/
theorem ctrlChain_emb_off (l i : AncL x) (hil : i ≠ l)
    (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    ctrlChain x l (ancEmbed (L₁ := SysL x) (oneHot x i) w)
      = ancEmbed (L₁ := SysL x) (oneHot x i) w := by
  rw [ctrlChain]
  refine chainOp_fix _ _ fun s => ?_
  have h := pairGate_ctrl_ancEmbed (L₁ := SysL x) l s (str x l s).gate (oneHot x i) w
  rwa [oneHot_ne x (Ne.symm hil), if_neg Bool.false_ne_true] at h

/-- The letter chain on the flag branch applies the whole Pauli string. -/
theorem ctrlChain_emb_at (l : AncL x)
    (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    ctrlChain x l (ancEmbed (L₁ := SysL x) (oneHot x l) w)
      = ancEmbed (L₁ := SysL x) (oneHot x l) (pauliString (str x l) w) := by
  rw [ctrlChain]
  have hstep : ∀ s : SysL x,
      regLift (ctrlReg x l s)
        ((pairGate (D := QubitCells (WL x)) (aC x l) (sC x s) Sum.inr_ne_inl
          (control (str x l s).gate)) :
          TSpace (QubitCells (WL x)) (ctrlReg x l s).toFun →ₗ[ℂ] _)
        (ancEmbed (L₁ := SysL x) (oneHot x l) (stringTake (str x l) (s : ℕ) w))
      = ancEmbed (L₁ := SysL x) (oneHot x l) (stringTake (str x l) ((s : ℕ) + 1) w) := by
    intro s
    have h := pairGate_ctrl_ancEmbed (L₁ := SysL x) l s (str x l s).gate (oneHot x l)
      (stringTake (str x l) (s : ℕ) w)
    rw [oneHot_self, if_pos rfl] at h
    refine h.trans ?_
    congr 1
    rw [stringTake_succ (str x l) (s : ℕ) s.isLt, LinearMap.comp_apply, Fin.eta]
  have key := chainOp_finRange_family _
    (fun m => ancEmbed (L₁ := SysL x) (oneHot x l) (stringTake (str x l) m w)) hstep
  have h0 : stringTake (str x l) 0 w = w := by
    rw [stringTake_zero, Module.End.one_apply]
  have htop : stringTake (str x l) (2 ^ x) w = pauliString (str x l) w := by
    rw [stringTake_top]
  rw [h0] at key
  rw [key, htop]

/-- One full rung on a generic branch family: branch `l` acquires its signed
Pauli string. -/
theorem rungOp_ohSum (τ : ST) (l : AncL x)
    (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    rungOp x τ l (ohSum x u)
      = ohSum x (Function.update u l
          (((sg x τ l : ℝ) : ℂ) • pauliString (str x l) (u l))) := by
  show ctrlChain x l (sgnL x τ l (ohSum x u)) = _
  rw [sgnL_ohSum, ohSum, ohSum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hil : i = l
  · subst hil
    rw [Function.update_self, Function.update_self, map_smul, map_smul,
      ctrlChain_emb_at, map_smul]
  · rw [Function.update_of_ne hil, Function.update_of_ne hil,
      ctrlChain_emb_off x l i hil]

/-- The SELECT stage profile on a generic branch family. -/
noncomputable def ohSel (τ : ST)
    (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (l : ℕ)
    (i : AncL x) : HS (QubitCells (SysL x)) (univ : Finset (SysL x)) :=
  if (i : ℕ) < l then ((sg x τ i : ℝ) : ℂ) • pauliString (str x i) (u i) else u i

theorem selPart_ohSum (τ : ST)
    (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (l : ℕ)
    (hl : l ≤ HubbardLCU.NT x) :
    selPart x τ l (ohSum x u) = ohSum x (ohSel x τ u l) := by
  induction l with
  | zero =>
      have h1 : ohSel x τ u 0 = u := by
        funext i
        simp [ohSel]
      rw [show selPart x τ 0 = 1 from rfl, Module.End.one_apply, h1]
  | succ l ih =>
      have hl' : l < HubbardLCU.NT x := by omega
      rw [selPart_succ x τ l hl', LinearMap.comp_apply, ih (by omega), rungOp_ohSum]
      congr 1
      funext i
      by_cases hi : i = (⟨l, hl'⟩ : AncL x)
      · subst hi
        rw [Function.update_self]
        simp only [ohSel]
        rw [if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _)]
      · have hne : (i : ℕ) ≠ l := fun hc => hi (Fin.ext hc)
        rw [Function.update_of_ne hi]
        simp only [ohSel]
        by_cases h2 : (i : ℕ) < l
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]

/-- **SELECT squares to the identity on the block**: applied to the fully
selected state it undoes every signed string (`sg² = 1`, `P² = 1`). -/
theorem selOp_selSt_top (τ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    selOp x τ (selSt x hx w τ (HubbardLCU.NT x)) = fullSt x hx w τ := by
  rw [selSt_eq_ohSum,
    show selOp x τ = selPart x τ (HubbardLCU.NT x) from rfl,
    selPart_ohSum x τ _ (HubbardLCU.NT x) le_rfl, fullSt_eq_ohSum]
  congr 1
  funext i
  simp only [ohSel]
  rw [if_pos i.isLt]
  rw [show selW x τ (HubbardLCU.NT x) i w
      = ((sg x τ i : ℝ) : ℂ) • pauliString (str x i) w from by
    rw [selW, if_pos i.isLt, LinearMap.smul_apply]]
  rw [map_smul, map_smul]
  rw [show pauliString (str x i) (pauliString (str x i) w) = w from by
    have h := LinearMap.ext_iff.mp (pauliString_comp_self (str x i)) w
    simpa using h]
  rw [smul_smul, smul_smul]
  congr 1
  have hsq : ((sg x τ i : ℝ) : ℂ) * ((sg x τ i : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, sg_sq x τ i, Complex.ofReal_one]
  calc ((sg x τ i : ℝ) : ℂ) * ((am x hx τ i : ℝ) : ℂ) * ((sg x τ i : ℝ) : ℂ)
      = ((am x hx τ i : ℝ) : ℂ) * (((sg x τ i : ℝ) : ℂ) * ((sg x τ i : ℝ) : ℂ)) := by
        ring
    _ = ((am x hx τ i : ℝ) : ℂ) := by rw [hsq, mul_one]

/-- **The pass squares to the identity on the block.** -/
theorem lcuOp_outSt (τ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    lcuOp x hx τ (outSt x hx w τ) = sysEmb x w := by
  show xLift x hx (unprepChain x hx τ (selOp x τ (prepChain x hx τ
    (xLift x hx (outSt x hx w τ))))) = _
  rw [show xLift x hx (outSt x hx w τ)
      = unprepChain x hx τ (selSt x hx w τ (HubbardLCU.NT x)) from by
    rw [show outSt x hx w τ = xLift x hx (unprepChain x hx τ
        (selSt x hx w τ (HubbardLCU.NT x))) from rfl, xLift_invol]]
  rw [prepChain_unprepChain, selOp_selSt_top,
    show unprepChain x hx τ (fullSt x hx w τ)
      = ancEmbed (L₁ := SysL x) (oneHot x (a0 x hx)) w from by
    rw [← prepChain_emb x hx τ w, unprepChain_prepChain]]
  exact xLift_oneHot_emb x hx w

/-! ## §13. The walker representation and the one-cell reflection/phase -/

/-- The Givens gate on the two flag branches it moves: the `∣01⟩` case
(`givens_vpair_01`), the mirror of the lane-(iii) `prep_gate_at`. -/
theorem upd_atB_swap (j : Fin (HubbardLCU.NT x - 1)) :
    Function.update (Function.update (oneHot x (jB x j)) (jA x j) true) (jB x j) false
      = oneHot x (jA x j) := by
  funext a
  rcases eq_or_ne a (jB x j) with rfl | h1
  · rw [Function.update_self]
    exact (oneHot_ne x (Ne.symm (jA_ne_jB_fin x j))).symm
  · rw [Function.update_of_ne h1]
    rcases eq_or_ne a (jA x j) with rfl | h2
    · rw [Function.update_self]
      exact (oneHot_self x _).symm
    · rw [Function.update_of_ne h2, oneHot_ne x h1]
      exact (oneHot_ne x h2).symm

theorem upd_atB_stay (j : Fin (HubbardLCU.NT x - 1)) :
    Function.update (Function.update (oneHot x (jB x j)) (jA x j) false) (jB x j) true
      = oneHot x (jB x j) := by
  funext a
  rcases eq_or_ne a (jB x j) with rfl | h1
  · rw [Function.update_self]
    exact (oneHot_self x _).symm
  · rw [Function.update_of_ne h1]
    rcases eq_or_ne a (jA x j) with rfl | h2
    · rw [Function.update_self]
      exact (oneHot_ne x (jA_ne_jB_fin x j)).symm
    · rw [Function.update_of_ne h2]

theorem prep_gate_atB (θ : ℝ) (j : Fin (HubbardLCU.NT x - 1))
    (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    regLift (prepReg x j)
        ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
          (jA_ne_jB x j) (givens θ)) :
          TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _)
        (ancEmbed (L₁ := SysL x) (oneHot x (jB x j)) w)
      = (-(Real.sin θ) : ℂ) • ancEmbed (L₁ := SysL x) (oneHot x (jA x j)) w
        + (Real.cos θ : ℂ) • ancEmbed (L₁ := SysL x) (oneHot x (jB x j)) w := by
  have hbc : oneHot x (jB x j) (jA x j) = false := oneHot_ne x (jA_ne_jB_fin x j)
  have hbd : oneHot x (jB x j) (jB x j) = true := oneHot_self x _
  have hpair_ne : ((true, false) : Bool × Bool) ≠ (false, true) := by decide
  have hG : (givens θ : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
      (vpair (qbit (oneHot x (jB x j) (jA x j))) (qbit (oneHot x (jB x j) (jB x j))))
      = ∑ q ∈ ({(true, false), (false, true)} : Finset (Bool × Bool)),
          (if q.1 then (-(Real.sin θ) : ℂ) else (Real.cos θ : ℂ)) •
            vpair (qbit (id q).1) (qbit (id q).2) := by
    rw [hbc, hbd, Finset.sum_pair hpair_ne]
    simp only [id_eq, if_true, if_false, Bool.false_eq_true]
    exact givens_vpair_01 θ
  have h := pairGate_anc_ancEmbed (L₁ := SysL x) (jA x j) (jB x j) (jA_ne_jB x j)
    (givens θ) (oneHot x (jB x j)) ({(true, false), (false, true)} : Finset (Bool × Bool))
    (fun q => if q.1 then (-(Real.sin θ) : ℂ) else (Real.cos θ : ℂ)) id hG w
  rw [Finset.sum_pair hpair_ne] at h
  simp only [id_eq, if_true, if_false, Bool.false_eq_true] at h
  rw [show Function.update (Function.update (oneHot x (jB x j)) (jA x j) true)
        (jB x j) false = oneHot x (jA x j) from upd_atB_swap x j,
    show Function.update (Function.update (oneHot x (jB x j)) (jA x j) false)
        (jB x j) true = oneHot x (jB x j) from upd_atB_stay x j] at h
  exact h

/-- A Givens gate preserves the one-hot sector (explicit branch mixing). -/
theorem givensGate_ohSum (θ : ℝ) (j : Fin (HubbardLCU.NT x - 1))
    (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    regLift (prepReg x j)
        ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
          (jA_ne_jB x j) (givens θ)) :
          TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _)
        (ohSum x u)
      = ohSum x (Function.update (Function.update u (jA x j)
          ((Real.cos θ : ℂ) • u (jA x j) + (-(Real.sin θ) : ℂ) • u (jB x j)))
          (jB x j)
          ((Real.sin θ : ℂ) • u (jA x j) + (Real.cos θ : ℂ) • u (jB x j))) := by
  rw [ohSum, ohSum, map_sum]
  refine sum_eq_of_eq_off_pair x (jA x j) (jB x j) (jA_ne_jB_fin x j) _ _ ?_ ?_
  · intro i hiA hiB
    rw [prep_gate_off x θ j i hiA hiB, Function.update_of_ne hiB,
      Function.update_of_ne hiA]
  · rw [prep_gate_at x θ j (u (jA x j)), prep_gate_atB x θ j (u (jB x j)),
      Function.update_of_ne (jA_ne_jB_fin x j), Function.update_self,
      Function.update_self, map_add, map_add, map_smul, map_smul, map_smul, map_smul]
    module

/-- The UNPREPARE chain preserves the one-hot sector. -/
theorem unprepChain_ohSum (τ : ST)
    (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    ∃ u', unprepChain x hx τ (ohSum x u) = ohSum x u' := by
  suffices h : ∀ (li : List (Fin (HubbardLCU.NT x - 1)))
      (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))),
      ∃ u', chainOp li
        (fun j => regLift (prepReg x j)
          ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
            (jA_ne_jB x j) (givens (-(ang x hx τ (j : ℕ) (jA_lt x j))))) :
            TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _))
        (ohSum x u) = ohSum x u' from h _ u
  intro li
  induction li with
  | nil => exact fun u => ⟨u, rfl⟩
  | cons j t ih =>
      intro u
      obtain ⟨u', hu'⟩ := ih (Function.update (Function.update u (jA x j)
        ((Real.cos (-(ang x hx τ (j : ℕ) (jA_lt x j))) : ℂ) • u (jA x j)
          + (-(Real.sin (-(ang x hx τ (j : ℕ) (jA_lt x j)))) : ℂ) • u (jB x j)))
        (jB x j)
        ((Real.sin (-(ang x hx τ (j : ℕ) (jA_lt x j))) : ℂ) • u (jA x j)
          + (Real.cos (-(ang x hx τ (j : ℕ) (jA_lt x j))) : ℂ) • u (jB x j)))
      refine ⟨u', ?_⟩
      rw [chainOp_apply_cons, givensGate_ohSum x (-(ang x hx τ (j : ℕ) (jA_lt x j))) j u]
      exact hu'

/-- The pattern of a walker branch: the one-hot flag with cell `a₀` set. -/
def oneHot0 (i : AncL x) : AncL x → Bool :=
  Function.update (oneHot x i) (a0 x hx) true

theorem upd_anc0_false :
    Function.update (anc0 x) (a0 x hx) false = anc0 x :=
  Function.update_eq_self _ _

theorem upd_oneHot_a0_false :
    Function.update (oneHot x (a0 x hx)) (a0 x hx) false = anc0 x := by
  funext a
  rcases eq_or_ne a (a0 x hx) with rfl | h
  · rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne h, oneHot_ne x h]
    rfl

/-- **The walker representation**: vacuum component plus branches whose
patterns all have cell `a₀` set. -/
noncomputable def wkSt (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    HS (QubitCells (WL x)) (univ : Finset (WL x)) :=
  ancEmbed (L₁ := SysL x) (anc0 x) (u (a0 x hx))
    + ∑ i ∈ (univ : Finset (AncL x)).erase (a0 x hx),
        ancEmbed (L₁ := SysL x) (oneHot0 x hx i) (u i)

/-- `X(a₀)` carries the one-hot sector to the walker representation: the
`a₀`-flag branch becomes the vacuum, every other branch keeps its flag and
sets cell `a₀`. -/
theorem xLift_ohSum (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    xLift x hx (ohSum x u) = wkSt x hx u := by
  rw [ohSum, map_sum,
    ← Finset.add_sum_erase _ (fun i => xLift x hx
      (ancEmbed (L₁ := SysL x) (oneHot x i) (u i))) (mem_univ (a0 x hx)),
    wkSt]
  congr 1
  · have hU : (X : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single (oneHot x (a0 x hx) (a0 x hx)) 1)
        = (1 : ℂ) • EuclideanSpace.single false 1 := by
      rw [oneHot_self, one_smul]
      exact X_q1
    have h := gateAt_inr_ancEmbed (L₁ := SysL x) (a0 x hx) X (oneHot x (a0 x hx)) hU
      (u (a0 x hx))
    rw [one_smul, upd_oneHot_a0_false] at h
    exact h
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hne : i ≠ a0 x hx := (Finset.mem_erase.mp hi).1
    have hU : (X : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single (oneHot x i (a0 x hx)) 1)
        = (1 : ℂ) • EuclideanSpace.single true 1 := by
      rw [oneHot_ne x (Ne.symm hne), one_smul]
      exact X_q0
    have h := gateAt_inr_ancEmbed (L₁ := SysL x) (a0 x hx) X (oneHot x i) hU (u i)
    rw [one_smul] at h
    exact h

theorem oneHot0_a0 (i : AncL x) : oneHot0 x hx i (a0 x hx) = true :=
  Function.update_self _ _ _

theorem anc0_ne_oneHot0 (i : AncL x) : anc0 x ≠ oneHot0 x hx i := by
  intro hc
  have h := congrFun hc (a0 x hx)
  rw [oneHot0_a0] at h
  exact Bool.false_ne_true h

/-- The vacuum block of a walker state is its vacuum branch. -/
theorem embAdj_wkSt (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    LinearMap.adjoint (sysEmb x) (wkSt x hx u) = u (a0 x hx) := by
  rw [wkSt, map_add, map_sum]
  have h1 := adjoint_ancEmbed_comp (L₁ := SysL x) (anc0 x) (anc0 x) (u (a0 x hx))
  rw [if_pos rfl] at h1
  rw [show LinearMap.adjoint (sysEmb x)
      (ancEmbed (L₁ := SysL x) (anc0 x) (u (a0 x hx))) = u (a0 x hx) from h1,
    Finset.sum_eq_zero, add_zero]
  intro i _
  have h2 := adjoint_ancEmbed_comp (L₁ := SysL x) (anc0 x) (oneHot0 x hx i) (u i)
  rw [if_neg (anc0_ne_oneHot0 x hx i)] at h2
  exact h2

/-- **`Z(a₀)` is the reflection on the walker sector**: it fixes the vacuum
branch and negates every cell-`a₀`-set branch, i.e. it acts as
`2∣0⟩⟨0∣ₐ − 1`. -/
theorem reflOp_wkSt (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    reflOp x hx (wkSt x hx u)
      = (2 : ℂ) • ancEmbed (L₁ := SysL x) (anc0 x) (u (a0 x hx)) - wkSt x hx u := by
  rw [wkSt, map_add, map_sum]
  have hU0 : (Z : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single (anc0 x (a0 x hx)) 1)
      = (1 : ℂ) • EuclideanSpace.single false 1 := by
    rw [one_smul]
    exact Z_q0
  have h0 := gateAt_inr_ancEmbed (L₁ := SysL x) (a0 x hx) Z (anc0 x) hU0 (u (a0 x hx))
  rw [one_smul, upd_anc0_false] at h0
  rw [show reflOp x hx (ancEmbed (L₁ := SysL x) (anc0 x) (u (a0 x hx)))
      = ancEmbed (L₁ := SysL x) (anc0 x) (u (a0 x hx)) from h0]
  have hbr : ∀ i ∈ (univ : Finset (AncL x)).erase (a0 x hx),
      reflOp x hx (ancEmbed (L₁ := SysL x) (oneHot0 x hx i) (u i))
        = -(ancEmbed (L₁ := SysL x) (oneHot0 x hx i) (u i)) := by
    intro i _
    have hU1 : (Z : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single (oneHot0 x hx i (a0 x hx)) 1)
        = (-1 : ℂ) • EuclideanSpace.single true 1 := by
      rw [oneHot0_a0]
      calc (Z : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single true 1)
          = -q1 := Z_q1
        _ = (-1 : ℂ) • EuclideanSpace.single true 1 := by
            rw [neg_one_smul]
            rfl
    have h := gateAt_inr_ancEmbed (L₁ := SysL x) (a0 x hx) Z (oneHot0 x hx i) hU1 (u i)
    rw [show Function.update (oneHot0 x hx i) (a0 x hx) true = oneHot0 x hx i from
        Function.update_idem _ _ _, neg_one_smul] at h
    exact h
  rw [Finset.sum_congr rfl hbr, Finset.sum_neg_distrib]
  module

/-- The coefficient action of the one-cell phase gate on the basis kets. -/
theorem phase_single (θ : ℝ) (b : Bool) :
    (phase θ : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single b 1)
      = (if b then Complex.exp (θ * Complex.I) else 1) •
          EuclideanSpace.single b 1 := by
  rw [phase, diagOp_single]
  ext c
  simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  rcases eq_or_ne c b with rfl | h
  · simp
  · simp [h]

/-- **`phase φ (a₀)` on the walker sector**: the vacuum branch is fixed, every
cell-`a₀`-set branch acquires `e^{iφ}` — the block phase `diag(1, e^{iφ})`. -/
theorem phOp_wkSt (φ : ℝ)
    (u : AncL x → HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    phOp x hx φ (wkSt x hx u)
      = ancEmbed (L₁ := SysL x) (anc0 x) (u (a0 x hx))
        + Complex.exp (φ * Complex.I) •
            (wkSt x hx u - ancEmbed (L₁ := SysL x) (anc0 x) (u (a0 x hx))) := by
  rw [wkSt, map_add, map_sum]
  have hU0 : (phase φ : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single (anc0 x (a0 x hx)) 1)
      = (1 : ℂ) • EuclideanSpace.single false 1 := by
    rw [show anc0 x (a0 x hx) = false from rfl, phase_single, if_neg Bool.false_ne_true]
  have h0 := gateAt_inr_ancEmbed (L₁ := SysL x) (a0 x hx) (phase φ) (anc0 x) hU0
    (u (a0 x hx))
  rw [one_smul, upd_anc0_false] at h0
  rw [show phOp x hx φ (ancEmbed (L₁ := SysL x) (anc0 x) (u (a0 x hx)))
      = ancEmbed (L₁ := SysL x) (anc0 x) (u (a0 x hx)) from h0]
  have hbr : ∀ i ∈ (univ : Finset (AncL x)).erase (a0 x hx),
      phOp x hx φ (ancEmbed (L₁ := SysL x) (oneHot0 x hx i) (u i))
        = Complex.exp (φ * Complex.I) •
            ancEmbed (L₁ := SysL x) (oneHot0 x hx i) (u i) := by
    intro i _
    have hU1 : (phase φ : 𝕢 →ₗ[ℂ] 𝕢)
        (EuclideanSpace.single (oneHot0 x hx i (a0 x hx)) 1)
        = Complex.exp (φ * Complex.I) • EuclideanSpace.single true 1 := by
      rw [oneHot0_a0, phase_single, if_pos rfl]
    have h := gateAt_inr_ancEmbed (L₁ := SysL x) (a0 x hx) (phase φ) (oneHot0 x hx i)
      hU1 (u i)
    rw [show Function.update (oneHot0 x hx i) (a0 x hx) true = oneHot0 x hx i from
        Function.update_idem _ _ _] at h
    exact h
  rw [Finset.sum_congr rfl hbr, ← Finset.smul_sum]
  module

theorem reflOp_emb (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    reflOp x hx (sysEmb x w) = sysEmb x w := by
  have hU0 : (Z : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single (anc0 x (a0 x hx)) 1)
      = (1 : ℂ) • EuclideanSpace.single false 1 := by
    rw [one_smul]
    exact Z_q0
  have h := gateAt_inr_ancEmbed (L₁ := SysL x) (a0 x hx) Z (anc0 x) hU0 w
  rw [one_smul, upd_anc0_false] at h
  exact h

theorem phOp_emb (φ : ℝ) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    phOp x hx φ (sysEmb x w) = sysEmb x w := by
  have hU0 : (phase φ : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single (anc0 x (a0 x hx)) 1)
      = (1 : ℂ) • EuclideanSpace.single false 1 := by
    rw [show anc0 x (a0 x hx) = false from rfl, phase_single, if_neg Bool.false_ne_true]
  have h := gateAt_inr_ancEmbed (L₁ := SysL x) (a0 x hx) (phase φ) (anc0 x) hU0 w
  rw [one_smul, upd_anc0_false] at h
  exact h

theorem embAdj_emb (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    LinearMap.adjoint (sysEmb x) (sysEmb x w) = w := by
  have h := adjoint_ancEmbed_comp (L₁ := SysL x) (anc0 x) (anc0 x) w
  rwa [if_pos rfl] at h

/-- The lane-(iii) output state lies in the walker sector. -/
theorem outSt_wk (τ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    ∃ u, outSt x hx w τ = wkSt x hx u := by
  obtain ⟨u', hu'⟩ := unprepChain_ohSum x hx τ
    (fun i => ((am x hx τ i : ℝ) : ℂ) • selW x τ (HubbardLCU.NT x) i w)
  refine ⟨u', ?_⟩
  rw [show outSt x hx w τ = xLift x hx (unprepChain x hx τ
      (selSt x hx w τ (HubbardLCU.NT x))) from rfl,
    selSt_eq_ohSum, hu', xLift_ohSum]

/-- **The one-cell `Z(a₀)` agrees with the reflection `2∣0⟩⟨0∣ₐ − 1` on the
pass output** — the honesty statement behind the constant-arity reflection. -/
theorem refl_outSt (τ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    reflOp x hx (outSt x hx w τ)
      = (2 : ℂ) • sysEmb x (LinearMap.adjoint (sysEmb x) (outSt x hx w τ))
        - outSt x hx w τ := by
  obtain ⟨u, hu⟩ := outSt_wk x hx τ w
  rw [hu, reflOp_wkSt, embAdj_wkSt]
  rfl

theorem ph_outSt (φ : ℝ) (τ : ST) (w : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    phOp x hx φ (outSt x hx w τ)
      = sysEmb x (LinearMap.adjoint (sysEmb x) (outSt x hx w τ))
        + Complex.exp (φ * Complex.I) •
            (outSt x hx w τ - sysEmb x (LinearMap.adjoint (sysEmb x) (outSt x hx w τ))) := by
  obtain ⟨u, hu⟩ := outSt_wk x hx τ w
  rw [hu, phOp_wkSt, embAdj_wkSt]
  rfl

/-! ## §14. Tier 2: the qubitization block, and Tier 3: the transfer -/

/-- The block value at a unit eigenvector: `E† (U (E v)) = (E/λ) • v`. -/
theorem embAdj_outSt_eig (τ : ST) (hlam : 0 < lam x τ)
    (v : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (E : ℝ)
    (heig : hubbardOp x τ.1 τ.2 v = (E : ℂ) • v) :
    LinearMap.adjoint (sysEmb x) (outSt x hx v τ) = ((E / lam x τ : ℝ) : ℂ) • v := by
  rw [show LinearMap.adjoint (sysEmb x) (outSt x hx v τ)
      = LinearMap.adjoint (ancEmbed (L₁ := SysL x) (anc0 x)) (outSt x hx v τ) from rfl,
    blockEncoding x hx v τ hlam, heig, smul_smul]
  congr 1
  push_cast
  rw [div_eq_inv_mul]

/-- **Tier 2, the qubitization data**: for a unit eigenvector `v` of the
Bravyi–Kitaev Fermi–Hubbard Hamiltonian with eigenvalue `E`, the system
embedding, the LCU pass, the one-cell reflection `Z(a₀)` and the one-cell
phase family form a qubitization block with block value `c = E/λ`
(`Qhl/Register/Qubitization.lean`). -/
theorem hubbard_qubitization (τ : ST) (hlam : 0 < lam x τ)
    (v : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (hv : ‖v‖ = 1) (E : ℝ)
    (heig : hubbardOp x τ.1 τ.2 v = (E : ℂ) • v) :
    Qubitization.IsQubitization (sysEmb x) (lcuOp x hx τ) (reflOp x hx) (phOp x hx) v
      (E / lam x τ) where
  emb_adj := embAdj_emb x
  norm_v := hv
  norm_walk := by
    rw [lcuOp_emb]
    exact norm_outSt x hx v hv τ
  block := by
    rw [lcuOp_emb]
    exact embAdj_outSt_eig x hx τ hlam v E heig
  walk_sq := by
    rw [lcuOp_emb, lcuOp_outSt]
  refl_emb := reflOp_emb x hx
  refl_walk := by
    rw [lcuOp_emb, refl_outSt, embAdj_outSt_eig x hx τ hlam v E heig, map_smul]
    push_cast
    module
  ph_emb := phOp_emb x hx
  ph_walk := fun φ => by
    rw [lcuOp_emb, ph_outSt, embAdj_outSt_eig x hx τ hlam v E heig, map_smul]

section Tier23

variable (τ : ST) (hlam : 0 < lam x τ)
variable (v : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (hv : ‖v‖ = 1)
variable (E : ℝ) (heig : hubbardOp x τ.1 τ.2 v = (E : ℂ) • v)
variable (hc : (E / lam x τ) ^ 2 < 1)

include hlam hv heig hc in
/-- **Tier 2, the rotation (first column)**: on the walker block the reflected
pass sends `∣0⟩ₐ ⊗ v` to `cos·(∣0⟩ₐ ⊗ v) − sin·u₁` with `cos = E/λ`. -/
theorem hubbard_walk_rot_emb :
    reflOp x hx (lcuOp x hx τ (sysEmb x v))
      = ((E / lam x τ : ℝ) : ℂ) • sysEmb x v
        - ((Qubitization.sVal (E / lam x τ) : ℝ) : ℂ) •
            Qubitization.u1 (sysEmb x) (lcuOp x hx τ) v (E / lam x τ) :=
  Qubitization.walk_rot_emb hc (hubbard_qubitization x hx τ hlam v hv E heig)

include hlam hv heig hc in
/-- **Tier 2, the rotation (second column)**: the reflected pass sends `u₁` to
`sin·(∣0⟩ₐ ⊗ v) + cos·u₁` — together with `hubbard_walk_rot_emb`,
`hubbard_refl_u1` and `refl_emb` this is the invariance of the 2D block under
both the reflection and the pass, with the pass acting as the rotation with
`cos = E/λ`. -/
theorem hubbard_walk_rot_u1 :
    reflOp x hx (lcuOp x hx τ
        (Qubitization.u1 (sysEmb x) (lcuOp x hx τ) v (E / lam x τ)))
      = ((Qubitization.sVal (E / lam x τ) : ℝ) : ℂ) • sysEmb x v
        + ((E / lam x τ : ℝ) : ℂ) •
            Qubitization.u1 (sysEmb x) (lcuOp x hx τ) v (E / lam x τ) :=
  Qubitization.walk_rot_u1 hc (hubbard_qubitization x hx τ hlam v hv E heig)

include hlam hv heig in
/-- The reflection negates the orthogonal partner. -/
theorem hubbard_refl_u1 :
    reflOp x hx (Qubitization.u1 (sysEmb x) (lcuOp x hx τ) v (E / lam x τ))
      = -Qubitization.u1 (sysEmb x) (lcuOp x hx τ) v (E / lam x τ) :=
  Qubitization.refl_u1 (hubbard_qubitization x hx τ hlam v hv E heig)

include hlam hv heig hc in
/-- **Tier 2, the QSP product identity**: the named output of the loop on the
eigenvector block input is the blockwise 2×2 matrix product — for an
arbitrary angle array `Φ`, the loop output decomposes over the orthonormal
block basis with coordinates the entries of `∏ₖ (R(E/λ)·diag(1, e^{iΦₖ}))`. -/
theorem hubbard_qsp_product (Φ : Fin d → ℝ) :
    qspSt x hx d v τ Φ d
      = Qubitization.qspProd (E / lam x τ) (phiSeq d Φ) d 0 0 • sysEmb x v
        + Qubitization.qspProd (E / lam x τ) (phiSeq d Φ) d 1 0 •
            Qubitization.u1 (sysEmb x) (lcuOp x hx τ) v (E / lam x τ) :=
  Qubitization.qsp_product (hubbard_qubitization x hx τ hlam v hv E heig) hc
    (phiSeq d Φ) d

include hlam hv heig hc in
/-- **Tier 3, the transfer corollary** (hypothesis-carrying): IF the QSP
product entry `P_Φ(E/λ)` is `ε`-close to a target amplitude, THEN the
post-selected (ancilla-vacuum) component of the loop output is `ε`-close to
`target • v`.  The existence of an angle array realizing a given target
polynomial (Jacobi–Anger etc., Low–Chuang 2019, Gilyén et al. 2019) is not
formalized; it enters exactly through this hypothesis. -/
theorem hubbard_qsp_transfer (Φ : Fin d → ℝ) (target : ℂ) (ε : ℝ)
    (hP : ‖Qubitization.qspPoly (E / lam x τ) (phiSeq d Φ) d - target‖ ≤ ε) :
    ‖LinearMap.adjoint (sysEmb x) (qspSt x hx d v τ Φ d) - target • v‖ ≤ ε :=
  Qubitization.qsp_transfer (hubbard_qubitization x hx τ hlam v hv E heig) hc
    (phiSeq d Φ) d target ε hP

end Tier23

end

end Qhl.HubbardQSP

/-! ## §15. Axiom audit -/

#print axioms Qhl.HubbardQSP.qspDeriv
#print axioms Qhl.HubbardQSP.qspValid
#print axioms Qhl.HubbardQSP.qspPre_expect_one
#print axioms Qhl.HubbardQSP.hubbard_qubitization
#print axioms Qhl.HubbardQSP.hubbard_walk_rot_emb
#print axioms Qhl.HubbardQSP.hubbard_walk_rot_u1
#print axioms Qhl.HubbardQSP.hubbard_refl_u1
#print axioms Qhl.HubbardQSP.hubbard_qsp_product
#print axioms Qhl.HubbardQSP.hubbard_qsp_transfer
#print axioms Qhl.HubbardQSP.refl_outSt
#print axioms Qhl.HubbardQSP.lcuOp_outSt

/-! # Hubbard QSP from source constructors -/
namespace Qhl.HubbardQSP.Source
open Qhl HubbardQSP HubbardLCU BravyiKitaev Finset
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal
variable (x : ℕ) (hx : 0 < x) (d : ℕ)

theorem rungIdentityQ (φ : STQc d → Prop)
    (hφ : ∀ σ v, φ ((cInnerQ d).set σ v) ↔ φ σ) :
    SourceDerivTot (SourceAssertion.identity (D := QubitCells (WL x)) φ)
      (((sgnBody x hx).mapStore StoreLens.fst).seq
        (countedProg (cInnerQ d) (fun _ => 2 ^ x)
          ((ctrlBody x hx).mapStore StoreLens.fst))) (SourceAssertion.identity (D := QubitCells
        (WL x)) φ) :=
  SourceDerivTot.seq
    (SourceDerivTot.unitary_identity (fun σ : STQc d => sgnRegE x hx σ.1)
      (fun σ : STQc d => sgnGateE x hx σ.1) _ (fun (_ : STQc d) _ => (Reg.single _).inj))
    (SourceDerivTot.countedIdentity (cInnerQ d) (fun _ => 2 ^ x) φ hφ (fun _ _ => rfl) _
      (SourceDerivTot.unitary_identity (fun σ : STQc d => ctrlRegE x hx σ.1)
        (fun σ : STQc d => ctrlGateE x hx σ.1) _ (fun (_ : STQc d) _ => (ctrlReg x _ _).inj))
      (fun _ => SourceDerivTot.unitary_identity (fun σ : STQc d => ctrlRegE x hx σ.1)
        (fun σ : STQc d => ctrlGateE x hx σ.1) _ (fun (_ : STQc d) _ => (ctrlReg x _ _).inj)))

theorem passIdentity (p : ℕ → Prop) :
    SourceDerivTot (SourceAssertion.identity (D := QubitCells (WL x)) (fun σ : STQc d => p (cnt
        d σ)))
      ((phaseProg x hx d).seq (wPassProg x hx d))
      (SourceAssertion.identity (D := QubitCells (WL x)) (fun σ : STQc d => p (cnt d σ))) := by
  refine SourceDerivTot.seq
    (SourceDerivTot.unitary_identity _ _ _ (fun _ _ => (Reg.single _).inj)) ?_
  let A : SourceAssertion (STQc d) (QubitCells (WL x)) :=
    SourceAssertion.identity (fun σ => p (cnt d σ))
  refine SourceDerivTot.seq (B := A) ?_
    (SourceDerivTot.seq (B := A) ?_ (SourceDerivTot.seq (B := A) ?_ ?_))
  · rw [prepQ_eq]
    refine SourceDerivTot.seq
      (SourceDerivTot.unitary_identity _ _ _ (fun _ _ => (Reg.single _).inj)) ?_
    exact SourceDerivTot.countedIdentity (cOuterQ d) _ _ (fun _ _ => Iff.rfl)
      (fun _ _ => rfl) _
      (SourceDerivTot.unitary_identity (fun σ : STQc d => prepRegE x hx σ.1)
        (fun σ : STQc d => prepGateE x hx σ.1) _ (fun (_ : STQc d) _ => (prepReg x _).inj))
      (fun _ => SourceDerivTot.unitary_identity (fun σ : STQc d => prepRegE x hx σ.1)
        (fun σ : STQc d => prepGateE x hx σ.1) _ (fun (_ : STQc d) _ => (prepReg x _).inj))
  · rw [selQ_eq]
    exact SourceDerivTot.countedIdentity (cOuterQ d) _ _ (fun _ _ => Iff.rfl)
      (fun _ _ => rfl) _
      (rungIdentityQ x hx d _ (fun _ _ => Iff.rfl))
      (fun _ => rungIdentityQ x hx d _ (fun _ _ => Iff.rfl))
  · rw [unprepQ_eq]
    refine SourceDerivTot.seq ?_
      (SourceDerivTot.unitary_identity _ _ _ (fun _ _ => (Reg.single _).inj))
    exact SourceDerivTot.countedIdentity (cOuterQ d) _ _ (fun _ _ => Iff.rfl)
      (fun _ _ => rfl) _
      (SourceDerivTot.unitary_identity (fun σ : STQc d => unprepRegE x hx σ.1)
        (fun σ : STQc d => unprepGateE x hx σ.1) _ (fun (_ : STQc d) _ => (prepReg x _).inj))
      (fun _ => SourceDerivTot.unitary_identity (fun σ : STQc d => unprepRegE x hx σ.1)
        (fun σ : STQc d => unprepGateE x hx σ.1) _ (fun (_ : STQc d) _ => (prepReg x _).inj))
  · exact SourceDerivTot.unitary_identity _ _ _ (fun _ _ => (Reg.single _).inj)

/-- Independent identity rank decrease of the actual QSP body. -/
theorem bodyIdentityRank (z : Int) :
    SourceDerivTot
      (SourceAssertion.identity (D := QubitCells (WL x))
        (fun σ : STQc d => True ∧ gdQ d σ = true ∧ (rank d σ : Int) = z))
      (bodyProg x hx d)
      (SourceAssertion.identity (D := QubitCells (WL x))
        (fun σ : STQc d => (rank d σ : Int) < z)) := by
  refine .seq (.conseq ?_
    (passIdentity x hx d (fun k => True ∧ decide (k < d) = true ∧ ((d-k : ℕ) : Int) = z))
    (SourceAssertion.entails_refl _)) (.conseq ?_ (.assign _ _) (SourceAssertion.entails_refl _))
  · exact SourceAssertion.entails_refl _
  · refine ⟨?_, fun _ _ => ⟨Iff.rfl, fun _ => le_rfl⟩⟩
    intro σ hσ
    have hlt : cnt d σ < d := by simpa using hσ.2.1
    change (↑(d - (σ.2.2 + 1)) : Int) < z
    change True ∧ decide (cnt d σ < d) = true ∧ (↑(d - cnt d σ) : Int) = z at hσ
    dsimp [cnt] at hσ hlt
    omega

variable (ψ : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (hψ : ‖ψ‖ = 1)

/-- A pure-state cq assertion under the QSP guard and a counter predicate. -/
noncomputable abbrev cq (v : STQc d → HS (QubitCells (WL x)) (univ : Finset (WL x)))
    (hv : ∀ σ, ‖v σ‖ = 1) (p : ℕ → Prop) :=
  SourceAssertion.ofAssn (Assn.ofStateFam v hv)
    (fun σ => gdQ d σ = true ∧ p (cnt d σ))

theorem phaseSource (p : ℕ → Prop) :
    SourceDerivTot (cq x d (st0 x hx d ψ) (norm_st0 x hx d ψ hψ) p)
      (phaseProg x hx d) (cq x d (st1 x hx d ψ) (norm_st1 x hx d ψ hψ) p) := by
  apply SourceDerivTot.countedRung_fam _ _ _ _
  intro σ _
  exact ⟨(Reg.single _).inj, rfl⟩

theorem prepSource (p : ℕ → Prop) :
    SourceDerivTot (cq x d (st1 x hx d ψ) (norm_st1 x hx d ψ hψ) p)
      (prepQ x hx d) (cq x d (st3 x hx d ψ) (norm_st3 x hx d ψ hψ) p) := by
  rw [prepQ_eq]
  refine .seq (B := cq x d (st2 x hx d ψ) (norm_st2 x hx d ψ hψ) p) ?_ ?_
  · apply SourceDerivTot.countedRung_fam _ _ _ _
    intro σ _
    exact ⟨(Reg.single _).inj, rfl⟩
  · apply SourceDerivTot.countedStateChainVar (cOuterQ d) (fun _ => HubbardLCU.NT x - 1)
      (fun σ => gdQ d σ = true ∧ p (cnt d σ))
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
      (prepPreQ x hx d ψ) (norm_prepPreQ x hx d ψ hψ) (fun _ _ _ => rfl)
      (fun _ _ => rfl) (fun σ _ => prepPreQ_full x hx d ψ σ)
    · exact SourceDerivTot.countedRung_fam _ _ _ _
        (fun σ h => prepBodyQ_act x hx d ψ σ σ.1.1 rfl h.2)
    · intro z
      exact SourceDerivTot.unitary_identity _ _ _ (fun σ _ => (prepReg x _).inj)

theorem selStepSource (p : ℕ → Prop) :
    SourceDerivTot
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun σ : STQc d => stSel x hx d ψ σ.1.1 σ)
          (fun σ => norm_stSel x hx d ψ hψ σ.1.1 σ))
        (fun σ => (gdQ d σ = true ∧ p (cnt d σ)) ∧ σ.1.1 < HubbardLCU.NT x))
      (((sgnBody x hx).mapStore StoreLens.fst).seq
        (countedProg (cInnerQ d) (fun _ => 2 ^ x)
          ((ctrlBody x hx).mapStore StoreLens.fst)))
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun σ : STQc d => stSel x hx d ψ (σ.1.1 + 1) σ)
          (fun σ => norm_stSel x hx d ψ hψ (σ.1.1 + 1) σ))
        (fun σ => (gdQ d σ = true ∧ p (cnt d σ)) ∧ σ.1.1 < HubbardLCU.NT x)) := by
  refine .seq (B := SourceAssertion.ofAssn
    (Assn.ofStateFam (fun σ : STQc d => sgnMidQ x hx d ψ σ.1.1 σ)
      (fun σ => norm_sgnMidQ x hx d ψ hψ σ.1.1 σ))
    (fun σ => (gdQ d σ = true ∧ p (cnt d σ)) ∧ σ.1.1 < HubbardLCU.NT x)) ?_ ?_
  · exact SourceDerivTot.countedRung_fam _ _ _ _
      (fun σ _ => sgnBodyQ_act x hx d ψ σ σ.1.1 rfl)
  · apply SourceDerivTot.countedStateChainVar (cInnerQ d) (fun _ => 2 ^ x)
      (fun σ => (gdQ d σ = true ∧ p (cnt d σ)) ∧ σ.1.1 < HubbardLCU.NT x)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
      (fun m σ => ctrlPreQ x hx d ψ σ.1.1 m σ)
      (fun m σ => norm_ctrlPreQ x hx d ψ hψ σ.1.1 m σ)
      (fun _ _ _ => rfl) (fun _ _ => rfl)
      (fun σ h => ctrlPreQ_full x hx d ψ σ σ.1.1 h.2)
    · exact SourceDerivTot.countedRung_fam _ _ _ _
        (fun σ h => ctrlBodyQ_act x hx d ψ σ σ.1.1 σ.1.2.1 rfl rfl h.2)
    · intro z
      exact SourceDerivTot.unitary_identity _ _ _ (fun σ _ => (ctrlReg x _ _).inj)

theorem selSource (p : ℕ → Prop) :
    SourceDerivTot (cq x d (st3 x hx d ψ) (norm_st3 x hx d ψ hψ) p)
      (selQ x hx d)
      (cq x d (stSel x hx d ψ (HubbardLCU.NT x))
        (norm_stSel x hx d ψ hψ (HubbardLCU.NT x)) p) := by
  rw [selQ_eq]
  apply SourceDerivTot.countedStateChainVar (cOuterQ d) (fun _ => HubbardLCU.NT x)
    (fun σ => gdQ d σ = true ∧ p (cnt d σ))
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (stSel x hx d ψ) (norm_stSel x hx d ψ hψ) (fun _ _ _ => rfl)
    (fun σ _ => by rw [stSel, show selPart x (coefQ d σ) 0 = 1 from rfl,
      Module.End.one_apply]) (fun _ _ => rfl)
  · exact selStepSource x hx d ψ hψ p
  · intro z
    exact rungIdentityQ x hx d _ (fun _ _ => Iff.rfl)

theorem unprepSource (p : ℕ → Prop) :
    SourceDerivTot
      (cq x d (stSel x hx d ψ (HubbardLCU.NT x))
        (norm_stSel x hx d ψ hψ (HubbardLCU.NT x)) p)
      (unprepQ x hx d) (cq x d (st6 x hx d ψ) (norm_st6 x hx d ψ hψ) p) := by
  rw [unprepQ_eq]
  refine .seq (B := cq x d (st5 x hx d ψ) (norm_st5 x hx d ψ hψ) p) ?_ ?_
  · apply SourceDerivTot.countedStateChainVar (cOuterQ d) (fun _ => HubbardLCU.NT x - 1)
      (fun σ => gdQ d σ = true ∧ p (cnt d σ))
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
      (unprepPreQ x hx d ψ) (norm_unprepPreQ x hx d ψ hψ) (fun _ _ _ => rfl)
      (fun _ _ => rfl) (fun σ _ => unprepPreQ_full x hx d ψ σ)
    · exact SourceDerivTot.countedRung_fam _ _ _ _
        (fun σ h => unprepBodyQ_act x hx d ψ σ σ.1.1 rfl h.2)
    · intro z
      exact SourceDerivTot.unitary_identity _ _ _ (fun σ _ => (prepReg x _).inj)
  · apply SourceDerivTot.countedRung_fam _ _ _ _
    intro σ _
    exact ⟨(Reg.single _).inj, rfl⟩

theorem reflSource (p : ℕ → Prop) :
    SourceDerivTot (cq x d (st6 x hx d ψ) (norm_st6 x hx d ψ hψ) p)
      (reflProg x hx d) (cq x d (st7 x hx d ψ) (norm_st7 x hx d ψ hψ) p) := by
  apply SourceDerivTot.countedRung_fam _ _ _ _
  intro σ _
  exact ⟨(Reg.single _).inj, rfl⟩

/-- The QSP program's own counter lens. -/
def counter : CounterLens (STQc d) where
  get := cnt d
  set σ k := (σ.1, σ.2.1, k)
  get_set _ _ := rfl

/-- The exact original QSP program and state endpoints through source rules. -/
theorem qspDeriv :
    SourceDerivTot (SourceAssertion.ofAssn (Ppre x d ψ hψ) (fun _ => True))
      (qspProg x hx d)
      (SourceAssertion.ofAssn (Qpost x hx d ψ hψ) (fun _ => True)) := by
  apply SourceDerivTot.countedStateChainVar (counter d) (fun _ => d) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun m σ => qspSt x hx d ψ (coefQ d σ) (phis d σ) m)
    (fun m σ => norm_qspSt x hx d ψ hψ (coefQ d σ) (phis d σ) m)
    (hv₀ := fun _ => norm_inS x ψ hψ)
    (hv₁ := fun σ => norm_qspSt x hx d ψ hψ (coefQ d σ) (phis d σ) d)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  · have hp := (phaseSource x hx d ψ hψ (fun _ => True)).seq
      ((prepSource x hx d ψ hψ (fun _ => True)).seq
        ((selSource x hx d ψ hψ (fun _ => True)).seq
          ((unprepSource x hx d ψ hψ (fun _ => True)).seq
            (reflSource x hx d ψ hψ (fun _ => True)))))
    refine .conseq ?_ hp ?_
    · apply SourceAssertion.entails_ofAssn
      · intro σ h
        exact ⟨by simpa [gdQ, counter] using h.2, trivial⟩
      · intro _ _; exact le_rfl
    · apply SourceAssertion.entails_ofAssn
      · intro σ h
        exact ⟨trivial, by simpa [gdQ, counter] using h.1⟩
      · intro σ _
        exact le_of_eq (congrArg (fun v => outerLM v v) (st7_eq x hx d ψ σ))
  · intro z
    exact passIdentity x hx d (fun k => True ∧ k < d ∧ (↑(d-k) : Int) = z)

/-- Original QSP semantic target from source soundness. -/
theorem qspValid : validTot (Ppre x d ψ hψ) (qspProg x hx d) (Qpost x hx d ψ hψ) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (qspDeriv x hx d ψ hψ).sound

end Qhl.HubbardQSP.Source

#print axioms Qhl.HubbardQSP.Source.bodyIdentityRank

#print axioms Qhl.HubbardQSP.Source.qspDeriv
#print axioms Qhl.HubbardQSP.Source.qspValid
