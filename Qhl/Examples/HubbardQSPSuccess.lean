import Qhl.Logic.Source.CountedStateChain
import Qhl.Logic.Source.CountedWp
import Qhl.Logic.Source.CountedFamily
import Qhl.Examples.HubbardLCUSuccess
import Qhl.Register.QubitizationBlock

/-!
# The QSP fidelity triple, internalized

`Qhl/Examples/HubbardQSPTriple.lean` proves the exact evolution triple of the
qubitization/QSP loop and, *outside* the proof system, the transfer bound
`hubbard_qsp_transfer` at a fixed store.  This file **internalizes** the
fidelity conclusion as a `DerivTot`-derived triple over *all* input states ρ
and *all* stores:

* every classical hypothesis becomes a **mask** on the precondition: the
  store `σ` is *ε-good* (`goodStore`) when the stored coefficients make `v`
  an eigenvector (`H(σ) v = E v`), `λ(σ) > 0`, the block value satisfies
  `(E/λ)² < 1`, and the QSP polynomial at the stored angle array is `ε`-close
  to the target amplitude `τ`;
* the fidelity conclusion becomes an **effect precondition**: the target
  projector `1_a ⊗ ∣v⟩⟨v∣` scaled by `c(τ,ε) = max(‖τ‖ − ε, 0)²`;
* the ancilla initialisation is part of the **program**, so (Ax-Init) turns
  the vacuum-sector compression into a valid global precondition.

**The triple** (`qspFidelityDeriv` / `qspFidelityValid`), for a unit `v` and
`0 ≤ ε`, `‖τ‖ ≤ 1 + ε`:

```
{ (c(τ,ε) • (1_a ⊗ ∣v⟩⟨v∣)).mask ε-good }
    q̄_a := ∣0…0⟩ ; k := 0 ; while k < d do phase ; walk ; k := k+1 od
{ ∣0…0⟩⟨0…0∣_a ⊗ ∣v⟩⟨v∣ }
```

over the enlarged store `STQc d = STc × (Fin d → ℝ) × ℕ` (the widened LCU
store with its two fragment counters, the angle array, the QSP counter; the
Hamiltonian coefficients read through `coefQ`), derived by (Ax-Init) +
(Ax-Ass) + one (Ax-Uni) per gate + (R-Seq) + the **ranked (R-Loop-tot)**
(rank `d − k`) + (R-Conseq).  Every loop of the walk pass is a genuine
counted `while` (`countedProg`), so the backward precondition of each
fragment loop is a **suffix weakest-precondition family** `wpSuffix`
(`Qhl/Logic/CountedWp.lean`): the one-unitary loops (PREPARE, UNPREPARE) are
each ONE `DerivTot.countedWpChain_const` call against a literal-index
transformer family, the compound SELECT loop is ONE
`DerivTot.countedWpBody_const` call whose step is the sign-gate
(Ax-Uni)/(R-Conseq) rung glued by (R-Seq) to the `φ`-relativised
`DerivTot.countedWpChain` of the inner letter loop — the counted-`wp` mirror
of the LCU lane (`Qhl/Examples/HubbardLCUSuccess.lean`), at the enlarged
store through the pulled-back counter lenses `cOuterQ`/`cInnerQ`.
**Reading**: for every input ρ, the probability that the loop output
post-selects onto the target state `∣0⟩_a ⊗ v` is at least
`(‖τ‖ − ε)² · Tr(ρ (1_a ⊗ ∣v⟩⟨v∣))` on ε-good stores.

The loop invariant is the **backward transformer form**: at counter `k`, the
wp of the target projector through the *remaining* `d − k` phased passes
(`walkRem`); the loop body preserves it exactly — each `wpSuffix` family is
displayed as one conjugation by its semantic chain operator
(`wpSuffix_zero_op_conj` plus the `chainOp` bridges of the LCU lane), so the
wp of the whole body is one conjugation by the phased pass (`wpBody_op`) —
and the rank `d − k` strictly decreases (`bodyStep`).  The final (R-Conseq)
entailment is where the qubitization theorems serve as conseq lemmas: the
whole-walk pulled-back vacuum vector is `conj(P_φ(E/λ)) • v` **exactly**
(`Qubitization.adjoint_passProd_block` — the invariance of the walk plane's
orthocomplement), so the wp compresses on the vacuum sector to
`|P_φ(E/λ)|² ∣v⟩⟨v∣ ≥ c(τ,ε) ∣v⟩⟨v∣` by the transfer estimate.

Non-vacuity (`fidPre_witness`): at even depth `d = 2m` with zero angles,
store `(t, U) = (0, 1)`, the vacuum pattern is an explicit eigenvector with
`E = 0`, the QSP entry is the unit `(−1)^m`, and the precondition expectation
at the input `∣0⟩_a ⊗ v` is exactly `c = 1 > 0` (with `τ = (−1)^m`, `ε = 0`).
-/

namespace Qhl.HubbardQSPSuccess

open Qhl Qhl.HubbardLCU Qhl.HubbardQSP Qhl.HubbardLCUSuccess Qhl.BravyiKitaev Finset
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal

section

variable (x : ℕ) (hx : 0 < x) (d : ℕ)

/-! ## §1. The program: ancilla initialisation, then the QSP loop -/

/-- **The QSP success program**: the literal ancilla initialisation, then the
counted phased-walk loop. -/
noncomputable def qspInitProg : Prog (STQc d) (QubitCells (WL x)) :=
  (Prog.init fun _ => ancS x).seq (qspProg x hx d)

/-! ## §2. The walk operators of the loop -/

/-- One phased pass at stored coefficients `τc` and angle `φ`. -/
noncomputable def passAt (τc : ST) (φ : ℝ) :
    EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  Qubitization.passOp (lcuOp x hx τc) (reflOp x hx) (phOp x hx) φ

theorem isUnitary_passAt (τc : ST) (φ : ℝ) : IsUnitary (passAt x hx τc φ) :=
  (isUnitary_reflOp x hx).comp ((isUnitary_lcuOp x hx τc).comp (isUnitary_phOp x hx φ))

/-- The product of the passes `k, …, k+n−1`. -/
noncomputable def walkN (τc : ST) (φs : ℕ → ℝ) (k n : ℕ) :
    EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  Qubitization.passProd (lcuOp x hx τc) (reflOp x hx) (phOp x hx) φs k n

theorem isUnitary_walkN (τc : ST) (φs : ℕ → ℝ) :
    ∀ (n k : ℕ), IsUnitary (walkN x hx τc φs k n)
  | 0, _ => isUnitary_one
  | n + 1, k =>
      (isUnitary_walkN τc φs n (k + 1)).comp (isUnitary_passAt x hx τc (φs k))

/-- The remaining walk at store `σ`: the passes `k, …, d−1` at the stored
coefficients (read through `coefQ`) and angles, `k` the stored counter. -/
noncomputable def walkRem (σ : STQc d) :
    EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  walkN x hx (coefQ d σ) (phiSeq d (phis d σ)) (cnt d σ) (d - cnt d σ)

/-! ## §3. The endpoint assertions and the loop invariant -/

variable (v : HS (QubitCells (SysL x)) (univ : Finset (SysL x)))

/-- The postcondition: the target projector `∣0…0⟩⟨0…0∣_a ⊗ ∣v⟩⟨v∣` — the
rank-one effect of the intended output state `∣0⟩_a ⊗ v`. -/
noncomputable def fidPost (hv : ‖v‖ = 1) : Assn (STQc d) (QubitCells (WL x)) :=
  Assn.ofStateFam (fun _ : STQc d => sysEmb x v) (fun _ => norm_inS x v hv)

variable (hv : ‖v‖ = 1)

/-- The loop invariant, in backward-transformer form: the wp of the target
projector through the remaining passes. -/
noncomputable def Jw : Assn (STQc d) (QubitCells (WL x)) where
  op σ := LinearMap.adjoint (walkRem x hx d σ) ∘ₗ
    outerLM (sysEmb x v) (sysEmb x v) ∘ₗ walkRem x hx d σ
  isEffect σ :=
    isEffect_conj (isEffect_outerLM_self (norm_inS x v hv))
      (le_of_eq (isUnitary_walkN x hx (coefQ d σ) (phiSeq d (phis d σ)) _ _).1)

@[simp]
theorem Jw_op (σ : STQc d) :
    (Jw x hx d v hv).op σ
      = LinearMap.adjoint (walkRem x hx d σ) ∘ₗ
          outerLM (sysEmb x v) (sysEmb x v) ∘ₗ walkRem x hx d σ := rfl

/-- The ε-good stores: `v` is an eigenvector of the stored Hamiltonian with
eigenvalue `E`, the one-norm is positive, the block value is nondegenerate,
and the stored QSP polynomial is `ε`-close to the target `τ` — all at the
coefficient block `coefQ` of the enlarged store. -/
def goodStore (E : ℝ) (τ : ℂ) (ε : ℝ) (σ : STQc d) : Prop :=
  hubbardOp x (coefQ d σ).1 (coefQ d σ).2 v = ((E : ℝ) : ℂ) • v ∧
    0 < lam x (coefQ d σ) ∧ (E / lam x (coefQ d σ)) ^ 2 < 1 ∧
    ‖Qubitization.qspPoly (E / lam x (coefQ d σ)) (phiSeq d (phis d σ)) d - τ‖ ≤ ε

/-- The unscaled target observable `1_a ⊗ ∣v⟩⟨v∣`. -/
noncomputable def sysProjA : Assn (STQc d) (QubitCells (WL x)) :=
  ⟨fun _ => sysLift (L₂ := AncL x) (outerLM v v),
    fun _ => isEffect_sysLift (isEffect_outerLM_self hv)⟩

theorem cScal_nonneg (τ : ℂ) (ε : ℝ) : 0 ≤ max (‖τ‖ - ε) 0 ^ 2 := by positivity

theorem cScal_le_one (τ : ℂ) (ε : ℝ) (hτ : ‖τ‖ ≤ 1 + ε) :
    max (‖τ‖ - ε) 0 ^ 2 ≤ 1 := by
  have h1 : max (‖τ‖ - ε) 0 ≤ 1 := max_le (by linarith) zero_le_one
  calc max (‖τ‖ - ε) 0 ^ 2 ≤ 1 ^ 2 := by
        exact pow_le_pow_left₀ (le_max_right _ _) h1 2
    _ = 1 := one_pow 2

/-- **The internalized fidelity precondition**: the target observable
`1_a ⊗ ∣v⟩⟨v∣` scaled by `c(τ,ε) = max(‖τ‖ − ε, 0)²`, masked by the ε-good
classical hypotheses. -/
noncomputable def fidPre (E : ℝ) (τ : ℂ) (ε : ℝ) (hτ : ‖τ‖ ≤ 1 + ε) :
    Assn (STQc d) (QubitCells (WL x)) :=
  ((sysProjA x d v hv).scaled (max (‖τ‖ - ε) 0 ^ 2) (cScal_nonneg τ ε)
    (cScal_le_one τ ε hτ)).mask (goodStore x d v E τ ε)

/-! ## §4. The literal-index transformer families of the loop body

Each counted fragment loop's body is a store-read (Ax-Uni); the counted-`wp`
rules consume a **literal-index** transformer family that agrees with the
store-read transformer on the step mask.  The families are the LCU-lane
families (`prepT`/`letterT`/`rungT`/`unprepT` of
`Qhl/Examples/HubbardLCUSuccess.lean`) transported to the enlarged store: the
gate angles/signs read the coefficient block through `coefQ`, and each family
is displayed as one conjugation by the corresponding LCU pass operator
(`prepG`/`letterG`/`rungOp`/`unprepG`). -/

/-- The store-computed phase gate of the current pass, as a named family
(named so that definitional comparisons never open the angle arithmetic). -/
noncomputable def phaseGU (σ : STQc d) :
    UnitaryOp (TSpace (QubitCells (WL x)) (Reg.single (aC x (a0 x hx))).toFun) :=
  singleGate (QubitCells (WL x)) (aC x (a0 x hx)) (phase (phiAt d σ))

/-- The literal-`k` backward transformer of one PREPARE pass: (Ax-Uni) at the
Givens pair of position `k`, the angle read through `coefQ`. -/
noncomputable def prepTQ (k : ℕ) (A : Assn (STQc d) (QubitCells (WL x))) :
    Assn (STQc d) (QubitCells (WL x)) :=
  A.unitaryPre (RegExpr.const (prepReg x (jCell x hx k)))
    (fun σ : STQc d => pairGate (D := QubitCells (WL x)) (aC x (jA x (jCell x hx k)))
      (aC x (jB x (jCell x hx k))) (jA_ne_jB x (jCell x hx k))
      (givens (ang x hx (coefQ d σ) ((jCell x hx k : Fin (HubbardLCU.NT x - 1)) : ℕ)
        (jA_lt x (jCell x hx k)))))

theorem prepTQ_op (k : ℕ) (A : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (prepTQ x hx d k A).op σ
      = LinearMap.adjoint (prepG x hx (coefQ d σ) k) ∘ₗ A.op σ ∘ₗ
          prepG x hx (coefQ d σ) k :=
  Assn.unitaryPre_const_op A (prepReg x (jCell x hx k))
    (fun σ' : STQc d => pairGate (D := QubitCells (WL x)) (aC x (jA x (jCell x hx k)))
      (aC x (jB x (jCell x hx k))) (jA_ne_jB x (jCell x hx k))
      (givens (ang x hx (coefQ d σ') ((jCell x hx k : Fin (HubbardLCU.NT x - 1)) : ℕ)
        (jA_lt x (jCell x hx k))))) σ

/-- The literal-`(k, m)` backward transformer of one letter pass of SELECT
rung `k`: (Ax-Uni) at the controlled letter of term `k`, site `m`. -/
noncomputable def letterTQ (k m : ℕ) (A : Assn (STQc d) (QubitCells (WL x))) :
    Assn (STQc d) (QubitCells (WL x)) :=
  A.unitaryPre (RegExpr.const (ctrlReg x (lCell x hx k) (sCell x m)))
    (fun _ : STQc d => pairGate (D := QubitCells (WL x)) (aC x (lCell x hx k))
      (sC x (sCell x m)) Sum.inr_ne_inl
      (control (str x (lCell x hx k) (sCell x m)).gate))

theorem letterTQ_op (k m : ℕ) (A : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (letterTQ x hx d k m A).op σ
      = LinearMap.adjoint (letterG x hx k m) ∘ₗ A.op σ ∘ₗ letterG x hx k m :=
  Assn.unitaryPre_const_op A (ctrlReg x (lCell x hx k) (sCell x m))
    (fun _ : STQc d => pairGate (D := QubitCells (WL x)) (aC x (lCell x hx k))
      (sC x (sCell x m)) Sum.inr_ne_inl
      (control (str x (lCell x hx k) (sCell x m)).gate)) σ

/-- The literal-`k` backward transformer of one whole SELECT rung: the suffix
`wp` family of the letter loop, then the sign-gate (Ax-Uni), the sign read
through `coefQ`. -/
noncomputable def rungTQ (k : ℕ) (A : Assn (STQc d) (QubitCells (WL x))) :
    Assn (STQc d) (QubitCells (WL x)) :=
  (wpSuffix (letterTQ x hx d k) (2 ^ x) A 0).unitaryPre
    (RegExpr.const (Reg.single (aC x (lCell x hx k))))
    (fun σ : STQc d => singleGate (QubitCells (WL x)) (aC x (lCell x hx k))
      (sgnGate (cf x (coefQ d σ) (lCell x hx k))))

/-- The rung transformer acts as one conjugation by the rung operator: the
sign-gate conjugation around the letter suffix family, collapsed through
`wpSuffix_zero_op_conj` and the letter chain bridge. -/
theorem rungTQ_op (k : ℕ) (A : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (rungTQ x hx d k A).op σ
      = LinearMap.adjoint (rungOp x (coefQ d σ) (lCell x hx k)) ∘ₗ A.op σ ∘ₗ
          rungOp x (coefQ d σ) (lCell x hx k) := by
  have h1 : (rungTQ x hx d k A).op σ
      = LinearMap.adjoint (sgnL x (coefQ d σ) (lCell x hx k)) ∘ₗ
          (wpSuffix (letterTQ x hx d k) (2 ^ x) A 0).op σ ∘ₗ
          sgnL x (coefQ d σ) (lCell x hx k) :=
    Assn.unitaryPre_const_op (wpSuffix (letterTQ x hx d k) (2 ^ x) A 0)
      (Reg.single (aC x (lCell x hx k)))
      (fun σ' : STQc d => singleGate (QubitCells (WL x)) (aC x (lCell x hx k))
        (sgnGate (cf x (coefQ d σ') (lCell x hx k)))) σ
  have h2 : (wpSuffix (letterTQ x hx d k) (2 ^ x) A 0).op σ
      = LinearMap.adjoint (chainOp (List.range (2 ^ x)) (letterG x hx k)) ∘ₗ
          A.op σ ∘ₗ chainOp (List.range (2 ^ x)) (letterG x hx k) :=
    wpSuffix_zero_op_conj (letterTQ x hx d k) (2 ^ x) A (letterG x hx k) σ
      (fun m _ A' => letterTQ_op x hx d k m A' σ)
  rw [h1, h2, chainOp_letterG x hx k,
    show rungOp x (coefQ d σ) (lCell x hx k)
      = ctrlChain x (lCell x hx k) ∘ₗ sgnL x (coefQ d σ) (lCell x hx k) from rfl,
    LinearMap.adjoint_comp]
  simp only [LinearMap.comp_assoc]

/-- The literal-`k` backward transformer of one UNPREPARE pass: (Ax-Uni) at
the Givens pair of the reversed position `N − 2 − k`, the inverse angle read
through `coefQ`. -/
noncomputable def unprepTQ (k : ℕ) (A : Assn (STQc d) (QubitCells (WL x))) :
    Assn (STQc d) (QubitCells (WL x)) :=
  A.unitaryPre (RegExpr.const (prepReg x (jCell x hx (HubbardLCU.NT x - 2 - k))))
    (fun σ : STQc d => pairGate (D := QubitCells (WL x))
      (aC x (jA x (jCell x hx (HubbardLCU.NT x - 2 - k))))
      (aC x (jB x (jCell x hx (HubbardLCU.NT x - 2 - k))))
      (jA_ne_jB x (jCell x hx (HubbardLCU.NT x - 2 - k)))
      (givens (-(ang x hx (coefQ d σ)
        ((jCell x hx (HubbardLCU.NT x - 2 - k) : Fin (HubbardLCU.NT x - 1)) : ℕ)
        (jA_lt x (jCell x hx (HubbardLCU.NT x - 2 - k)))))))

theorem unprepTQ_op (k : ℕ) (A : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (unprepTQ x hx d k A).op σ
      = LinearMap.adjoint (unprepG x hx (coefQ d σ) k) ∘ₗ A.op σ ∘ₗ
          unprepG x hx (coefQ d σ) k :=
  Assn.unitaryPre_const_op A (prepReg x (jCell x hx (HubbardLCU.NT x - 2 - k)))
    (fun σ' : STQc d => pairGate (D := QubitCells (WL x))
      (aC x (jA x (jCell x hx (HubbardLCU.NT x - 2 - k))))
      (aC x (jB x (jCell x hx (HubbardLCU.NT x - 2 - k))))
      (jA_ne_jB x (jCell x hx (HubbardLCU.NT x - 2 - k)))
      (givens (-(ang x hx (coefQ d σ')
        ((jCell x hx (HubbardLCU.NT x - 2 - k) : Fin (HubbardLCU.NT x - 1)) : ℕ)
        (jA_lt x (jCell x hx (HubbardLCU.NT x - 2 - k))))))) σ

/-! ## §4b. The backward `wp` tower of the loop body -/

/-- wp through the reflection (after the counter increment). -/
noncomputable def wpB1 (Y : Assn (STQc d) (QubitCells (WL x))) :
    Assn (STQc d) (QubitCells (WL x)) :=
  (Y.comp fun σ : STQc d => (σ.1, σ.2.1, σ.2.2 + 1)).unitaryPre
    (RegExpr.const (Reg.single (aC x (a0 x hx))))
    (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) Z)

/-- wp through the final `X(a₀)` of UNPREPARE. -/
noncomputable def wpB2 (Y : Assn (STQc d) (QubitCells (WL x))) :
    Assn (STQc d) (QubitCells (WL x)) :=
  (wpB1 x hx d Y).unitaryPre (RegExpr.const (Reg.single (aC x (a0 x hx))))
    (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)

/-- wp through the counted inverse-Givens loop of UNPREPARE: the suffix
family of the `unprepTQ` passes at entry. -/
noncomputable def wpB3 (Y : Assn (STQc d) (QubitCells (WL x))) :
    Assn (STQc d) (QubitCells (WL x)) :=
  wpSuffix (unprepTQ x hx d) (HubbardLCU.NT x - 1) (wpB2 x hx d Y) 0

/-- wp through SELECT: the suffix family of the `rungTQ` passes at entry. -/
noncomputable def wpB4 (Y : Assn (STQc d) (QubitCells (WL x))) :
    Assn (STQc d) (QubitCells (WL x)) :=
  wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) 0

/-- wp through the counted Givens loop of PREPARE. -/
noncomputable def wpB5 (Y : Assn (STQc d) (QubitCells (WL x))) :
    Assn (STQc d) (QubitCells (WL x)) :=
  wpSuffix (prepTQ x hx d) (HubbardLCU.NT x - 1) (wpB4 x hx d Y) 0

/-- wp through the `X(a₀)` of PREPARE. -/
noncomputable def wpB6 (Y : Assn (STQc d) (QubitCells (WL x))) :
    Assn (STQc d) (QubitCells (WL x)) :=
  (wpB5 x hx d Y).unitaryPre (RegExpr.const (Reg.single (aC x (a0 x hx))))
    (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)

/-- **The wp of the whole loop body**: the phase gate outermost. -/
noncomputable def wpBody (Y : Assn (STQc d) (QubitCells (WL x))) :
    Assn (STQc d) (QubitCells (WL x)) :=
  (wpB6 x hx d Y).unitaryPre (RegExpr.const (Reg.single (aC x (a0 x hx))))
    (phaseGU x hx d)

/-! ## §5. The wp display of the loop body -/

theorem wpB1_op (Y : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (wpB1 x hx d Y).op σ
      = LinearMap.adjoint (reflOp x hx) ∘ₗ
          Y.op (σ.1, σ.2.1, σ.2.2 + 1) ∘ₗ reflOp x hx :=
  Assn.unitaryPre_const_op _ (Reg.single (aC x (a0 x hx)))
    (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) Z) σ

theorem wpB2_op (Y : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (wpB2 x hx d Y).op σ
      = LinearMap.adjoint (xLift x hx) ∘ₗ (wpB1 x hx d Y).op σ ∘ₗ xLift x hx :=
  Assn.unitaryPre_const_op _ (Reg.single (aC x (a0 x hx)))
    (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X) σ

theorem wpB3_op (Y : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (wpB3 x hx d Y).op σ
      = LinearMap.adjoint (unprepChain x hx (coefQ d σ)) ∘ₗ (wpB2 x hx d Y).op σ ∘ₗ
          unprepChain x hx (coefQ d σ) := by
  refine (wpSuffix_zero_op_conj (unprepTQ x hx d) (HubbardLCU.NT x - 1)
    (wpB2 x hx d Y) (unprepG x hx (coefQ d σ)) σ
    (fun j _ A => unprepTQ_op x hx d j A σ)).trans ?_
  rw [chainOp_unprepG x hx (coefQ d σ)]

theorem wpB4_op (Y : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (wpB4 x hx d Y).op σ
      = LinearMap.adjoint (selOp x (coefQ d σ)) ∘ₗ (wpB3 x hx d Y).op σ ∘ₗ
          selOp x (coefQ d σ) := by
  refine (wpSuffix_zero_op_conj (rungTQ x hx d) (HubbardLCU.NT x)
    (wpB3 x hx d Y) (fun k => rungOp x (coefQ d σ) (lCell x hx k)) σ
    (fun k _ A => rungTQ_op x hx d k A σ)).trans ?_
  rw [chainOp_rungG x hx (coefQ d σ)]

theorem wpB5_op (Y : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (wpB5 x hx d Y).op σ
      = LinearMap.adjoint (prepChain x hx (coefQ d σ)) ∘ₗ (wpB4 x hx d Y).op σ ∘ₗ
          prepChain x hx (coefQ d σ) := by
  refine (wpSuffix_zero_op_conj (prepTQ x hx d) (HubbardLCU.NT x - 1)
    (wpB4 x hx d Y) (prepG x hx (coefQ d σ)) σ
    (fun j _ A => prepTQ_op x hx d j A σ)).trans ?_
  rw [chainOp_prepG x hx (coefQ d σ)]

theorem wpB6_op (Y : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (wpB6 x hx d Y).op σ
      = LinearMap.adjoint (xLift x hx) ∘ₗ (wpB5 x hx d Y).op σ ∘ₗ xLift x hx :=
  Assn.unitaryPre_const_op _ (Reg.single (aC x (a0 x hx)))
    (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X) σ

/-- **The wp display of the loop body**: one conjugation by the phased pass,
around the postcondition at the incremented counter. -/
theorem wpBody_op (Y : Assn (STQc d) (QubitCells (WL x))) (σ : STQc d) :
    (wpBody x hx d Y).op σ
      = LinearMap.adjoint (passAt x hx (coefQ d σ) (phiAt d σ)) ∘ₗ
          Y.op (σ.1, σ.2.1, σ.2.2 + 1) ∘ₗ passAt x hx (coefQ d σ) (phiAt d σ) := by
  have hph : (wpBody x hx d Y).op σ
      = LinearMap.adjoint (phOp x hx (phiAt d σ)) ∘ₗ (wpB6 x hx d Y).op σ ∘ₗ
          phOp x hx (phiAt d σ) :=
    Assn.unitaryPre_const_op _ (Reg.single (aC x (a0 x hx))) (phaseGU x hx d) σ
  rw [hph, wpB6_op x hx d Y σ, wpB5_op x hx d Y σ, wpB4_op x hx d Y σ,
    wpB3_op x hx d Y σ, wpB2_op x hx d Y σ, wpB1_op x hx d Y σ,
    show passAt x hx (coefQ d σ) (phiAt d σ)
      = reflOp x hx ∘ₗ
          ((((xLift x hx ∘ₗ unprepChain x hx (coefQ d σ)) ∘ₗ selOp x (coefQ d σ)) ∘ₗ
            (prepChain x hx (coefQ d σ) ∘ₗ xLift x hx)) ∘ₗ phOp x hx (phiAt d σ)) from rfl]
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_comp, LinearMap.adjoint_comp, LinearMap.adjoint_comp]
  simp only [LinearMap.comp_assoc]

/-! ## §5b. Counter-write insensitivity

Both pulled-back fragment lenses write only the embedded LCU counters
(`σ.1.1` / `σ.1.2.1`), while `coefQ` reads `σ.1.2.2` and the QSP data read
`σ.2`, so every transformer preserves counter-write insensitivity — the
`hg`/`hY` obligations of the counted-`wp` rules, discharged through the
conjugation displays and `wpSuffix_op_set`. -/

theorem prepTQ_op_set (c : CounterLens (STQc d))
    (hc : ∀ σ v, coefQ d (c.set σ v) = coefQ d σ) (k : ℕ)
    (A : Assn (STQc d) (QubitCells (WL x)))
    (hA : ∀ σ v, A.op (c.set σ v) = A.op σ) (σ : STQc d) (v : ℕ) :
    (prepTQ x hx d k A).op (c.set σ v) = (prepTQ x hx d k A).op σ := by
  rw [prepTQ_op, prepTQ_op, hA σ v, hc σ v]

theorem letterTQ_op_set (c : CounterLens (STQc d)) (k m : ℕ)
    (A : Assn (STQc d) (QubitCells (WL x)))
    (hA : ∀ σ v, A.op (c.set σ v) = A.op σ) (σ : STQc d) (v : ℕ) :
    (letterTQ x hx d k m A).op (c.set σ v) = (letterTQ x hx d k m A).op σ := by
  rw [letterTQ_op, letterTQ_op, hA σ v]

theorem rungTQ_op_set (c : CounterLens (STQc d))
    (hc : ∀ σ v, coefQ d (c.set σ v) = coefQ d σ) (k : ℕ)
    (A : Assn (STQc d) (QubitCells (WL x)))
    (hA : ∀ σ v, A.op (c.set σ v) = A.op σ) (σ : STQc d) (v : ℕ) :
    (rungTQ x hx d k A).op (c.set σ v) = (rungTQ x hx d k A).op σ := by
  rw [rungTQ_op, rungTQ_op, hA σ v, hc σ v]

theorem unprepTQ_op_set (c : CounterLens (STQc d))
    (hc : ∀ σ v, coefQ d (c.set σ v) = coefQ d σ) (k : ℕ)
    (A : Assn (STQc d) (QubitCells (WL x)))
    (hA : ∀ σ v, A.op (c.set σ v) = A.op σ) (σ : STQc d) (v : ℕ) :
    (unprepTQ x hx d k A).op (c.set σ v) = (unprepTQ x hx d k A).op σ := by
  rw [unprepTQ_op, unprepTQ_op, hA σ v, hc σ v]

theorem wpB1_op_set (c : CounterLens (STQc d))
    (hcomm : ∀ (σ : STQc d) (v : ℕ),
      ((((c.set σ v).1, (c.set σ v).2.1, (c.set σ v).2.2 + 1)) : STQc d)
        = c.set (σ.1, σ.2.1, σ.2.2 + 1) v)
    (Y : Assn (STQc d) (QubitCells (WL x)))
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ) (σ : STQc d) (v : ℕ) :
    (wpB1 x hx d Y).op (c.set σ v) = (wpB1 x hx d Y).op σ := by
  rw [wpB1_op, wpB1_op, hcomm σ v, hY (σ.1, σ.2.1, σ.2.2 + 1) v]

theorem wpB2_op_set (c : CounterLens (STQc d))
    (hcomm : ∀ (σ : STQc d) (v : ℕ),
      ((((c.set σ v).1, (c.set σ v).2.1, (c.set σ v).2.2 + 1)) : STQc d)
        = c.set (σ.1, σ.2.1, σ.2.2 + 1) v)
    (Y : Assn (STQc d) (QubitCells (WL x)))
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ) (σ : STQc d) (v : ℕ) :
    (wpB2 x hx d Y).op (c.set σ v) = (wpB2 x hx d Y).op σ := by
  rw [wpB2_op, wpB2_op, wpB1_op_set x hx d c hcomm Y hY σ v]

theorem wpB3_op_set (c : CounterLens (STQc d))
    (hcomm : ∀ (σ : STQc d) (v : ℕ),
      ((((c.set σ v).1, (c.set σ v).2.1, (c.set σ v).2.2 + 1)) : STQc d)
        = c.set (σ.1, σ.2.1, σ.2.2 + 1) v)
    (hc : ∀ σ v, coefQ d (c.set σ v) = coefQ d σ)
    (Y : Assn (STQc d) (QubitCells (WL x)))
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ) (σ : STQc d) (v : ℕ) :
    (wpB3 x hx d Y).op (c.set σ v) = (wpB3 x hx d Y).op σ :=
  wpSuffix_op_set (unprepTQ x hx d) (wpB2 x hx d Y) c
    (fun k A hA σ' v' => unprepTQ_op_set x hx d c hc k A hA σ' v')
    (fun σ' v' => wpB2_op_set x hx d c hcomm Y hY σ' v') 0 σ v

theorem wpB4_op_set (c : CounterLens (STQc d))
    (hcomm : ∀ (σ : STQc d) (v : ℕ),
      ((((c.set σ v).1, (c.set σ v).2.1, (c.set σ v).2.2 + 1)) : STQc d)
        = c.set (σ.1, σ.2.1, σ.2.2 + 1) v)
    (hc : ∀ σ v, coefQ d (c.set σ v) = coefQ d σ)
    (Y : Assn (STQc d) (QubitCells (WL x)))
    (hY : ∀ σ v, Y.op (c.set σ v) = Y.op σ) (σ : STQc d) (v : ℕ) :
    (wpB4 x hx d Y).op (c.set σ v) = (wpB4 x hx d Y).op σ :=
  wpSuffix_op_set (rungTQ x hx d) (wpB3 x hx d Y) c
    (fun k A hA σ' v' => rungTQ_op_set x hx d c hc k A hA σ' v')
    (fun σ' v' => wpB3_op_set x hx d c hcomm hc Y hY σ' v') 0 σ v

/-! ## §5c. The fragment derivations: one packaged counted-`wp` call per loop -/

/-- **PREPARE backward**: the `X(a₀)` (Ax-Uni), then ONE
`countedWpChain_const` call along the `prepTQ` suffix family over the
pulled-back outer lens; the agreement of the store-read body with the
literal family is definitional on the step mask. -/
theorem prepWpDerivQ (Y : Assn (STQc d) (QubitCells (WL x)))
    (hYo : ∀ σ v, Y.op ((cOuterQ d).set σ v) = Y.op σ) :
    DerivTot (wpB6 x hx d Y) (prepQ x hx d) (wpB4 x hx d Y) := by
  rw [prepQ_eq]
  refine DerivTot.seq (B := wpB5 x hx d Y)
    (DerivTot.unitary (RegExpr.const (Reg.single (aC x (a0 x hx))))
      (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)
      (wpB5 x hx d Y)) ?_
  have h : DerivTot (wpSuffix (prepTQ x hx d) (HubbardLCU.NT x - 1) (wpB4 x hx d Y) 0)
      (countedProg (cOuterQ d) (fun _ => HubbardLCU.NT x - 1)
        (Prog.unitary 2 (fun σ : STQc d => prepRegE x hx σ.1)
          (fun σ : STQc d => prepGateE x hx σ.1)))
      ((wpB4 x hx d Y).mask fun σ => (cOuterQ d).get σ = HubbardLCU.NT x - 1) :=
    DerivTot.countedWpChain_constSource (cOuterQ d)
      (fun σ : STQc d => prepRegE x hx σ.1) (fun σ : STQc d => prepGateE x hx σ.1)
      (prepTQ x hx d) (wpB4 x hx d Y)
      (fun k A hA σ v => prepTQ_op_set x hx d (cOuterQ d) (fun _ _ => rfl) k A hA σ v)
      (fun σ v => wpB4_op_set x hx d (cOuterQ d) (fun _ _ => rfl) (fun _ _ => rfl)
        Y hYo σ v)
      (fun σ _ => (prepReg x _).inj)
      (fun k _ σ hget A => by subst hget; rfl)
  exact DerivTot.conseq (Assn.le_refl' _) h
    (Assn.mask_le_of_imp_le fun σ _ => le_rfl)

/-- The sign gate of SELECT rung `k`, as the first half of the masked step
obligation of the outer counted loop: (Ax-Uni) + on-mask (R-Conseq) via
`unitary_stepMask`. -/
theorem sgnStepWpQ (Y : Assn (STQc d) (QubitCells (WL x))) (k : ℕ) :
    DerivTot
      ((wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) k).mask
        fun σ => (cOuterQ d).get σ = k ∧ k < HubbardLCU.NT x)
      ((sgnBody x hx).mapStore StoreLens.fst)
      ((wpSuffix (letterTQ x hx d k) (2 ^ x)
          (wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) (k + 1)) 0).mask
        fun σ => (cOuterQ d).get σ = k ∧ k < HubbardLCU.NT x) := by
  refine DerivTot.unitary_stepMask (fun σ : STQc d => sgnRegE x hx σ.1)
    (fun σ : STQc d => sgnGateE x hx σ.1) fun σ hσ => ?_
  obtain ⟨hget, hkn⟩ := hσ
  rw [Assn.unitaryPre_mask_op, Assn.mask_op_of_pos ⟨hget, hkn⟩,
    wpSuffix_of_lt hkn]
  refine le_of_eq ?_
  subst hget
  rfl

/-- The letter loop of SELECT rung `k`, relativised at the outer step mask:
ONE `countedWpChain` call along the `letterTQ k` suffix family over the
pulled-back inner lens. -/
theorem letterLoopWpQ (Y : Assn (STQc d) (QubitCells (WL x)))
    (hYi : ∀ σ v, Y.op ((cInnerQ d).set σ v) = Y.op σ) (k : ℕ) :
    DerivTot
      ((wpSuffix (letterTQ x hx d k) (2 ^ x)
          (wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) (k + 1)) 0).mask
        fun σ => (cOuterQ d).get σ = k ∧ k < HubbardLCU.NT x)
      (countedProg (cInnerQ d) (fun _ => 2 ^ x)
        ((ctrlBody x hx).mapStore StoreLens.fst))
      ((wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) (k + 1)).mask
        fun σ => (cOuterQ d).get σ = k ∧ k < HubbardLCU.NT x) := by
  have h : DerivTot
      ((wpSuffix (letterTQ x hx d k) (2 ^ x)
          (wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) (k + 1)) 0).mask
        fun σ => (cOuterQ d).get σ = k ∧ k < HubbardLCU.NT x)
      (countedProg (cInnerQ d) (fun _ => 2 ^ x)
        (Prog.unitary 2 (fun σ : STQc d => ctrlRegE x hx σ.1)
          (fun σ : STQc d => ctrlGateE x hx σ.1)))
      ((wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) (k + 1)).mask
        fun σ => ((cOuterQ d).get σ = k ∧ k < HubbardLCU.NT x)
          ∧ (cInnerQ d).get σ = 2 ^ x) :=
    DerivTot.countedWpChainSource (cInnerQ d)
      (fun σ : STQc d => ctrlRegE x hx σ.1) (fun σ : STQc d => ctrlGateE x hx σ.1)
      (letterTQ x hx d k)
      (wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) (k + 1))
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
      (fun m A hA σ v => letterTQ_op_set x hx d (cInnerQ d) k m A hA σ v)
      (fun σ v => wpSuffix_op_set (rungTQ x hx d) (wpB3 x hx d Y) (cInnerQ d)
        (fun k' A hA σ' v' => rungTQ_op_set x hx d (cInnerQ d)
          (fun _ _ => rfl) k' A hA σ' v')
        (fun σ' v' => wpB3_op_set x hx d (cInnerQ d) (fun _ _ => rfl)
          (fun _ _ => rfl) Y hYi σ' v')
        (k + 1) σ v)
      (fun σ _ _ => (ctrlReg x _ _).inj)
      (fun m _ σ hφ hget A => by
        obtain ⟨hout, -⟩ := hφ
        subst hget
        subst hout
        rfl)
  exact DerivTot.conseq (Assn.le_refl' _) h
    (Assn.mask_le_mask (fun σ hσ => hσ.1) (fun σ _ => le_rfl))

/-- SELECT's weighted invariant is preserved at the current outer counter;
the inner source loop reads that same outer counter throughout. -/
theorem selStepWpQSource (Y : Assn (STQc d) (QubitCells (WL x)))
    (hYi : ∀ σ v, Y.op ((cInnerQ d).set σ v) = Y.op σ) :
    DerivTot
      ((Assn.ofFam (cOuterQ d).get
        (wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y))).mask
        fun σ => σ.1.1 < HubbardLCU.NT x)
      (((sgnBody x hx).mapStore StoreLens.fst).seq
        (countedProg (cInnerQ d) (fun _ => 2 ^ x)
          ((ctrlBody x hx).mapStore StoreLens.fst)))
      ((Assn.ofFam (cOuterQ d).get
        (fun k => wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) (k + 1))).mask
        fun σ => σ.1.1 < HubbardLCU.NT x) := by
  let J : ℕ → Assn (STQc d) (QubitCells (WL x)) := fun m =>
    Assn.ofFam (cOuterQ d).get fun k =>
      wpSuffix (letterTQ x hx d k) (2 ^ x)
        (wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) (k + 1)) m
  refine DerivTot.seq (B := (J 0).mask fun σ => σ.1.1 < HubbardLCU.NT x) ?_ ?_
  · refine DerivTot.unitary_stepMask (fun σ : STQc d => sgnRegE x hx σ.1)
      (fun σ : STQc d => sgnGateE x hx σ.1) fun σ hσ => ?_
    rw [Assn.unitaryPre_mask_op,
      Assn.mask_op_of_pos (φ := fun σ : (STQc d) => σ.1.1 < HubbardLCU.NT x) hσ,
      Assn.ofFam_op]
    simp only [cOuterQ, CounterLens.pullbackFst, CounterLens.pullback, StoreLens.fst,
      Function.comp_apply, CounterLens.fst3]
    rw [wpSuffix_of_lt hσ]
    change (rungTQ x hx d σ.1.1 _).op σ ≤
      ((Assn.ofFam (cOuterQ d).get _).unitaryPre _ _).op σ
    rw [Assn.unitaryPre_ofFam_op]
    exact le_rfl
  · refine DerivTot.conseq (Assn.le_refl' _)
      (DerivTot.countedWhileSource (cInnerQ d) (J := J) (n := 2 ^ x)
        (fun _ _ => Iff.rfl) (fun _ _ => rfl) ?_ ?_ ?_) ?_
    · intro m σ v
      change (wpSuffix (letterTQ x hx d σ.1.1) (2 ^ x)
        (wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) (σ.1.1 + 1)) m).op
          ((cInnerQ d).set σ v) = _
      apply wpSuffix_op_set (letterTQ x hx d σ.1.1) _ (cInnerQ d)
        (fun k A hA σ' v' => letterTQ_op_set x hx d (cInnerQ d) σ.1.1 k A hA σ' v')
      intro σ' v'
      exact wpSuffix_op_set (rungTQ x hx d) (wpB3 x hx d Y) (cInnerQ d)
        (fun k A hA τ w => rungTQ_op_set x hx d (cInnerQ d)
          (fun _ _ => rfl) k A hA τ w)
        (fun τ w => wpB3_op_set x hx d (cInnerQ d) (fun _ _ => rfl) (fun _ _ => rfl) Y hYi τ w)
        (σ.1.1 + 1) σ' v'
    · refine DerivTot.unitary_stepMask (fun σ : STQc d => ctrlRegE x hx σ.1)
        (fun σ : STQc d => ctrlGateE x hx σ.1) fun σ hσ => ?_
      rw [Assn.unitaryPre_mask_op,
        Assn.mask_op_of_pos (φ := fun σ : (STQc d) => σ.1.1 < HubbardLCU.NT x ∧
          (cInnerQ d).get σ < 2 ^ x) hσ,
        Assn.ofFam_op]
      simp only [J, Assn.ofFam_op, cInnerQ, cOuterQ, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst, Function.comp_apply,
        CounterLens.snd3, CounterLens.fst3]
      have hm : σ.1.2.1 < 2 ^ x := hσ.2
      rw [wpSuffix_of_lt hm]
      rw [Assn.unitaryPre_ofFam_op]
      rw [Assn.unitaryPre_ofFam_op]
      exact le_rfl
    · intro k
      exact DerivTot.unitary_identity_mask (fun σ : STQc d => ctrlRegE x hx σ.1)
        (fun σ : STQc d => ctrlGateE x hx σ.1)
        (fun σ _ => (ctrlReg x _ _).inj)
    · apply Assn.mask_le_mask (fun _ h => h.1)
      intro σ _
      simp only [J, Assn.ofFam_op, cOuterQ, CounterLens.pullbackFst, CounterLens.pullback,
        StoreLens.fst, Function.comp_apply, CounterLens.fst3, wpSuffix_full]
      exact le_rfl

/-- **SELECT backward**: ONE `countedWpBody_const` call along the `rungTQ`
suffix family, its step the sign-gate rung glued to the relativised letter
loop by (R-Seq). -/
theorem selWpDerivQ (Y : Assn (STQc d) (QubitCells (WL x)))
    (hYo : ∀ σ v, Y.op ((cOuterQ d).set σ v) = Y.op σ)
    (hYi : ∀ σ v, Y.op ((cInnerQ d).set σ v) = Y.op σ) :
    DerivTot (wpB4 x hx d Y) (selQ x hx d) (wpB3 x hx d Y) := by
  rw [selQ_eq]
  have h : DerivTot (wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) 0)
      (countedProg (cOuterQ d) (fun _ => HubbardLCU.NT x)
        (((sgnBody x hx).mapStore StoreLens.fst).seq
          (countedProg (cInnerQ d) (fun _ => 2 ^ x)
            ((ctrlBody x hx).mapStore StoreLens.fst))))
      ((wpB3 x hx d Y).mask fun σ => (cOuterQ d).get σ = HubbardLCU.NT x) :=
    DerivTot.countedWpBody_constSource (cOuterQ d) (rungTQ x hx d) (wpB3 x hx d Y)
      (fun k A hA σ v => rungTQ_op_set x hx d (cOuterQ d) (fun _ _ => rfl) k A hA σ v)
      (fun σ v => wpB3_op_set x hx d (cOuterQ d) (fun _ _ => rfl) (fun _ _ => rfl)
        Y hYo σ v)
      (selStepWpQSource x hx d Y hYi)
      (fun _ => rungIdentityQ x hx d _ (fun _ _ => Iff.rfl))
  exact DerivTot.conseq (Assn.le_refl' _) h
    (Assn.mask_le_of_imp_le fun σ _ => le_rfl)

/-- **UNPREPARE backward**: ONE `countedWpChain_const` call along the
`unprepTQ` suffix family, then the `X(a₀)` (Ax-Uni). -/
theorem unprepWpDerivQ (Y : Assn (STQc d) (QubitCells (WL x)))
    (hYo : ∀ σ v, Y.op ((cOuterQ d).set σ v) = Y.op σ) :
    DerivTot (wpB3 x hx d Y) (unprepQ x hx d) (wpB1 x hx d Y) := by
  rw [unprepQ_eq]
  refine DerivTot.seq (B := wpB2 x hx d Y) ?_
    (DerivTot.unitary (RegExpr.const (Reg.single (aC x (a0 x hx))))
      (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)
      (wpB1 x hx d Y))
  have h : DerivTot (wpSuffix (unprepTQ x hx d) (HubbardLCU.NT x - 1) (wpB2 x hx d Y) 0)
      (countedProg (cOuterQ d) (fun _ => HubbardLCU.NT x - 1)
        (Prog.unitary 2 (fun σ : STQc d => unprepRegE x hx σ.1)
          (fun σ : STQc d => unprepGateE x hx σ.1)))
      ((wpB2 x hx d Y).mask fun σ => (cOuterQ d).get σ = HubbardLCU.NT x - 1) :=
    DerivTot.countedWpChain_constSource (cOuterQ d)
      (fun σ : STQc d => unprepRegE x hx σ.1) (fun σ : STQc d => unprepGateE x hx σ.1)
      (unprepTQ x hx d) (wpB2 x hx d Y)
      (fun k A hA σ v => unprepTQ_op_set x hx d (cOuterQ d) (fun _ _ => rfl) k A hA σ v)
      (fun σ v => wpB2_op_set x hx d (cOuterQ d) (fun _ _ => rfl) Y hYo σ v)
      (fun σ _ => (prepReg x _).inj)
      (fun k _ σ hget A => by subst hget; rfl)
  exact DerivTot.conseq (Assn.le_refl' _) h
    (Assn.mask_le_of_imp_le fun σ _ => le_rfl)

/-- The loop-body derivation at an arbitrary counter-write-insensitive
postcondition: (Ax-Ass) for the counter, one (Ax-Uni) per single gate, each
counted fragment loop one packaged counted-`wp` call. -/
theorem bodyWpDeriv (Y : Assn (STQc d) (QubitCells (WL x)))
    (hYo : ∀ σ v, Y.op ((cOuterQ d).set σ v) = Y.op σ)
    (hYi : ∀ σ v, Y.op ((cInnerQ d).set σ v) = Y.op σ) :
    DerivTot (wpBody x hx d Y) (bodyProg x hx d) Y := by
  show DerivTot (wpBody x hx d Y)
    (((phaseProg x hx d).seq (wPassProg x hx d)).seq
      (Prog.assign fun σ : STQc d => (σ.1, σ.2.1, σ.2.2 + 1))) Y
  refine DerivTot.seq (B := Y.comp fun σ : STQc d => (σ.1, σ.2.1, σ.2.2 + 1)) ?_
    (DerivTot.assign _ Y)
  refine DerivTot.seq (B := wpB6 x hx d Y)
    (DerivTot.unitary (RegExpr.const (Reg.single (aC x (a0 x hx))))
      (phaseGU x hx d) (wpB6 x hx d Y)) ?_
  show DerivTot (wpB6 x hx d Y)
    ((prepQ x hx d).seq ((selQ x hx d).seq ((unprepQ x hx d).seq (reflProg x hx d)))) _
  exact DerivTot.seq (prepWpDerivQ x hx d Y hYo)
    (DerivTot.seq (selWpDerivQ x hx d Y hYo hYi)
      (DerivTot.seq (unprepWpDerivQ x hx d Y hYo)
        (DerivTot.unitary (RegExpr.const (Reg.single (aC x (a0 x hx))))
          (fun _ : STQc d => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) Z)
          (Y.comp fun σ : STQc d => (σ.1, σ.2.1, σ.2.2 + 1)))))

/-! ## §6. The ranked loop derivation -/

/-- The remaining walk splits off its first pass under the guard. -/
theorem walkRem_split (σ : STQc d) (hlt : cnt d σ < d) :
    walkRem x hx d σ
      = walkRem x hx d (σ.1, σ.2.1, σ.2.2 + 1) ∘ₗ
          passAt x hx (coefQ d σ) (phiAt d σ) := by
  show walkN x hx (coefQ d σ) (phiSeq d (phis d σ)) (cnt d σ) (d - cnt d σ) = _
  rw [show d - cnt d σ = (d - cnt d σ - 1) + 1 from by omega]
  rw [show walkN x hx (coefQ d σ) (phiSeq d (phis d σ)) (cnt d σ) ((d - cnt d σ - 1) + 1)
      = walkN x hx (coefQ d σ) (phiSeq d (phis d σ)) (cnt d σ + 1) (d - cnt d σ - 1) ∘ₗ
          passAt x hx (coefQ d σ) (phiSeq d (phis d σ) (cnt d σ)) from
    Qubitization.passProd_succ _ _ _ _ _ _]
  rfl

/-- One pass of the loop at rank value `n`: the invariant is preserved
exactly, the rank strictly decreases.  (The masked invariant is insensitive
to the embedded fragment-counter writes, definitionally — the `hYo`/`hYi`
obligations of `bodyWpDeriv`.) -/
theorem bodyStep (n : ℕ) :
    DerivTot (((Jw x hx d v hv).mand (gdQ d)).mask fun σ => rank d σ = n)
      (bodyProg x hx d)
      ((Jw x hx d v hv).mask fun σ => rank d σ < n) := by
  refine DerivTot.conseq ?_
    (bodyWpDeriv x hx d ((Jw x hx d v hv).mask fun σ => rank d σ < n)
      (fun _ _ => rfl) (fun _ _ => rfl))
    (Assn.le_refl' _)
  intro σ
  by_cases hm : rank d σ = n
  · by_cases hg : gdQ d σ = true
    · have hlt : cnt d σ < d := by simpa [gdQ] using hg
      have hrk : rank d ((σ.1, σ.2.1, σ.2.2 + 1) : STQc d) < n := by
        have h1 : d - σ.2.2 = n := hm
        have h2 : σ.2.2 < d := hlt
        show d - (σ.2.2 + 1) < n
        omega
      refine le_of_eq ?_
      rw [Assn.mask_op_of_pos
          (A := (Jw x hx d v hv).mand (gdQ d)) hm,
        Assn.mand_op_of_true (A := Jw x hx d v hv) hg,
        wpBody_op x hx d _ σ,
        Assn.mask_op_of_pos (A := Jw x hx d v hv) hrk, Jw_op, Jw_op,
        walkRem_split x hx d σ hlt, adjoint_comp_conj]
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := (Jw x hx d v hv).mand (gdQ d)) hm]
      exact Assn.mand_op_of_false (A := Jw x hx d v hv) (by simpa using hg)
  · exact Assn.op_zero_le (Assn.mask_op_of_neg
      (A := (Jw x hx d v hv).mand (gdQ d)) hm)

/-- The backward invariant is preserved by a complete pass without a rank mask. -/
theorem bodyInvariantDeriv :
    DerivTot ((Jw x hx d v hv).mand (gdQ d)) (bodyProg x hx d) (Jw x hx d v hv) := by
  refine DerivTot.conseq ?_
    (bodyWpDeriv x hx d (Jw x hx d v hv) (fun _ _ => rfl) (fun _ _ => rfl))
    (Assn.le_refl' _)
  intro σ
  by_cases hg : gdQ d σ = true
  · have hlt : cnt d σ < d := by simpa [gdQ] using hg
    refine le_of_eq ?_
    rw [Assn.mand_op_of_true hg, wpBody_op, Jw_op, Jw_op,
      walkRem_split x hx d σ hlt, adjoint_comp_conj]
  · exact Assn.op_zero_le (Assn.mand_op_of_false (by simpa using hg))

/-- **(R-Loop-tot)** with rank `d − k`: definite termination, no meta-level
rule. -/
theorem loopDeriv :
    DerivTot (Jw x hx d v hv) (Prog.while (gdQ d) (bodyProg x hx d))
      ((Jw x hx d v hv).mandNot (gdQ d)) := by
  have ht : (Jw x hx d v hv).mask (fun _ => True) = Jw x hx d v hv := by
    ext σ; simp
  have h := DerivTot.whileLoopSource (A := Jw x hx d v hv) (φ := fun _ => True)
    (fun σ => (rank d σ : Int)) (fun _ _ => Int.natCast_nonneg _)
    (by simpa only [ht] using bodyInvariantDeriv x hx d v hv)
    (fun z => DerivTot.conseq
      (Assn.mask_le_mask (A := (Assn.one : Assn (STQc d) (QubitCells (WL x))))
        (B := Assn.one)
        (fun σ hσ => ⟨le_of_lt (by simpa [gdQ] using hσ.2.1), hσ.2⟩)
        (fun _ _ => le_rfl))
      (HubbardQSP.bodyIdentityRankDeriv x hx d z) (Assn.le_refl' _))
  simpa only [ht] using h

/-- Loop exit: past the bound the remaining walk is empty, so the invariant
is the target projector. -/
theorem post_le :
    (Jw x hx d v hv).mandNot (gdQ d) ≤ fidPost x d v hv := by
  intro σ
  by_cases hg : gdQ d σ = true
  · exact Assn.op_zero_le (Assn.mandNot_op_of_true (A := Jw x hx d v hv) hg)
  · have hσ : d ≤ cnt d σ := by simpa [gdQ] using hg
    refine le_of_eq ?_
    rw [Assn.mandNot_op_of_false (A := Jw x hx d v hv) (by simpa using hg), Jw_op,
      show walkRem x hx d σ = 1 from by
        show walkN x hx (coefQ d σ) (phiSeq d (phis d σ)) (cnt d σ) (d - cnt d σ) = 1
        rw [show d - cnt d σ = 0 from by omega]
        rfl,
      LinearMap.adjoint_one, Module.End.one_eq_id, LinearMap.id_comp,
      LinearMap.comp_id]
    rfl

/-! ## §7. The (R-Conseq) entailment at the initialisation -/

/-- The whole-loop wp of the target projector, compressed on the vacuum
sector: exactly `|P_φ(E/λ)|² ∣v⟩⟨v∣`, by the adjoint block value of the
walk. -/
theorem init_block_eq (E : ℝ) (σ : STQc d)
    (heig : hubbardOp x (coefQ d σ).1 (coefQ d σ).2 v = ((E : ℝ) : ℂ) • v)
    (hlam : 0 < lam x (coefQ d σ)) (hcsq : (E / lam x (coefQ d σ)) ^ 2 < 1) :
    LinearMap.adjoint (sysEmb x) ∘ₗ
        ((Jw x hx d v hv).comp fun σ' : STQc d => (σ'.1, σ'.2.1, 0)).op σ ∘ₗ sysEmb x
      = ((Complex.normSq
            (Qubitization.qspPoly (E / lam x (coefQ d σ))
              (phiSeq d (phis d σ)) d) : ℝ) : ℂ) •
          outerLM v v := by
  have hq := hubbard_qubitization x hx (coefQ d σ) hlam v hv E heig
  have hpass : ∀ φ, IsIsometryOp
      (Qubitization.passOp (lcuOp x hx (coefQ d σ)) (reflOp x hx) (phOp x hx) φ) :=
    fun φ => (isUnitary_passAt x hx (coefQ d σ) φ).isIsometryOp
  have hblock := Qubitization.adjoint_passProd_block hq hcsq hpass
    (phiSeq d (phis d σ)) d
  set W := Qubitization.passProd (lcuOp x hx (coefQ d σ)) (reflOp x hx) (phOp x hx)
    (phiSeq d (phis d σ)) 0 d with hW
  set p := Qubitization.qspPoly (E / lam x (coefQ d σ)) (phiSeq d (phis d σ)) d with hp
  have hcollapse : LinearMap.adjoint (sysEmb x) ∘ₗ
      (LinearMap.adjoint W ∘ₗ outerLM (sysEmb x v) (sysEmb x v) ∘ₗ W) ∘ₗ sysEmb x
      = outerLM (LinearMap.adjoint (W ∘ₗ sysEmb x) (sysEmb x v))
          (LinearMap.adjoint (W ∘ₗ sysEmb x) (sysEmb x v)) := by
    rw [← adjoint_comp_outerLM_self_comp (W ∘ₗ sysEmb x) (sysEmb x v),
      LinearMap.adjoint_comp]
    simp only [LinearMap.comp_assoc]
  have hpull : LinearMap.adjoint (W ∘ₗ sysEmb x) (sysEmb x v)
      = (starRingEnd ℂ) p • v := by
    rw [LinearMap.adjoint_comp, LinearMap.comp_apply]
    exact hblock
  have houter : outerLM ((starRingEnd ℂ) p • v) ((starRingEnd ℂ) p • v)
      = ((Complex.normSq p : ℝ) : ℂ) • outerLM v v := by
    refine LinearMap.ext fun u => ?_
    rw [outerLM_apply, LinearMap.smul_apply, outerLM_apply, inner_smul_left,
      Complex.conj_conj, smul_smul, smul_smul]
    congr 1
    calc p * (⟪v, u⟫ : ℂ) * (starRingEnd ℂ) p
        = p * (starRingEnd ℂ) p * ⟪v, u⟫ := by ring
      _ = ((Complex.normSq p : ℝ) : ℂ) * ⟪v, u⟫ := by rw [Complex.mul_conj]
  calc LinearMap.adjoint (sysEmb x) ∘ₗ
      ((Jw x hx d v hv).comp (fun σ' : STQc d => (σ'.1, σ'.2.1, 0))).op σ ∘ₗ sysEmb x
      = LinearMap.adjoint (sysEmb x) ∘ₗ
          (LinearMap.adjoint W ∘ₗ outerLM (sysEmb x v) (sysEmb x v) ∘ₗ W) ∘ₗ
          sysEmb x := rfl
    _ = outerLM (LinearMap.adjoint (W ∘ₗ sysEmb x) (sysEmb x v))
          (LinearMap.adjoint (W ∘ₗ sysEmb x) (sysEmb x v)) := hcollapse
    _ = ((Complex.normSq p : ℝ) : ℂ) • outerLM v v := by rw [hpull, houter]

/-- **The conseq entailment at the initialisation**: on ε-good stores, the
scaled target observable entails (Ax-Init)'s transformer of the loop wp. -/
theorem fidPre_le_init (E : ℝ) (τ : ℂ) (ε : ℝ) (hτ : ‖τ‖ ≤ 1 + ε) :
    fidPre x d v hv E τ ε hτ
      ≤ ((Jw x hx d v hv).comp fun σ' : STQc d => (σ'.1, σ'.2.1, 0)).initPre
          fun _ : STQc d => ancS x := by
  intro σ
  by_cases hgood : goodStore x d v E τ ε σ
  · obtain ⟨heig, hlam, hcsq, hqsp⟩ := id hgood
    rw [show (fidPre x d v hv E τ ε hτ).op σ
        = ((sysProjA x d v hv).scaled (max (‖τ‖ - ε) 0 ^ 2) (cScal_nonneg τ ε)
            (cScal_le_one τ ε hτ)).op σ from Assn.mask_op_of_pos hgood,
      Assn.scaled_op,
      show (sysProjA x d v hv).op σ = sysLift (L₂ := AncL x) (outerLM v v) from rfl]
    have hinit : (((Jw x hx d v hv).comp fun σ' : STQc d => (σ'.1, σ'.2.1, 0)).initPre
        fun _ : STQc d => ancS x).op σ
        = sysLift (L₂ := AncL x)
            (LinearMap.adjoint (sysEmb x) ∘ₗ
              ((Jw x hx d v hv).comp fun σ' : STQc d => (σ'.1, σ'.2.1, 0)).op σ ∘ₗ
              sysEmb x) :=
      initPre_ancCells_op (L₁ := SysL x) (L₂ := AncL x) _ σ
    rw [hinit, init_block_eq x hx d v hv E σ heig hlam hcsq, sysLift_smul]
    -- the scalar comparison: `c(τ,ε) ≤ |P_φ(E/λ)|²`
    set p := Qubitization.qspPoly (E / lam x (coefQ d σ)) (phiSeq d (phis d σ)) d with hp
    have hnorm : max (‖τ‖ - ε) 0 ≤ ‖p‖ := by
      have htri : |‖p‖ - ‖τ‖| ≤ ‖p - τ‖ := abs_norm_sub_norm_le p τ
      have h1 : ‖τ‖ - ε ≤ ‖p‖ := by
        have := abs_le.mp htri
        linarith
      exact max_le h1 (norm_nonneg p)
    have hscal : max (‖τ‖ - ε) 0 ^ 2 ≤ Complex.normSq p := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (le_max_right _ _) hnorm 2
    exact real_smul_le_real_smul hscal
      (isPositive_sysLift (isPositive_outerLM_self v))
  · exact Assn.op_zero_le (Assn.mask_op_of_neg hgood)

/-! ## §8. The fidelity triple and soundness -/

/-- **The QSP fidelity triple**, derived in the printed system
((Ax-Init) + (Ax-Ass) + (Ax-Uni) + (R-Seq) + ranked (R-Loop-tot) + (R-Conseq);
the fragment loops through the counted-`wp` layer, itself packaged from these
printed rules):

```
{ (c(τ,ε) • (1_a ⊗ ∣v⟩⟨v∣)).mask ε-good }
    q̄_a := ∣0…0⟩ ; k := 0 ; while k < d do phase ; walk ; k := k+1 od
{ ∣0…0⟩⟨0…0∣_a ⊗ ∣v⟩⟨v∣ } ,      c(τ,ε) = max(‖τ‖ − ε, 0)² .
```
-/
theorem qspFidelityDeriv (E : ℝ) (τ : ℂ) (ε : ℝ) (hτ : ‖τ‖ ≤ 1 + ε) :
    DerivTot (fidPre x d v hv E τ ε hτ) (qspInitProg x hx d) (fidPost x d v hv) := by
  refine DerivTot.conseq (fidPre_le_init x hx d v hv E τ ε hτ)
    (DerivTot.seq
      (DerivTot.initProg _
        ((Jw x hx d v hv).comp fun σ' : STQc d => (σ'.1, σ'.2.1, 0)))
      ?_)
    (Assn.le_refl' _)
  show DerivTot _ ((Prog.assign fun σ : STQc d => (σ.1, σ.2.1, 0)).seq
    (Prog.while (gdQ d) (bodyProg x hx d))) _
  exact DerivTot.conseq (Assn.le_refl' _)
    (DerivTot.seq (DerivTot.assign _ (Jw x hx d v hv)) (loopDeriv x hx d v hv))
    (post_le x hx d v hv)

/-- **Soundness**: over every input ρ and every store, the expected value of
the masked scaled target observable lower-bounds the probability of
post-selecting the output onto `∣0⟩_a ⊗ v`. -/
theorem qspFidelityValid (E : ℝ) (τ : ℂ) (ε : ℝ) (hτ : ‖τ‖ ≤ 1 + ε) :
    validTot (fidPre x d v hv E τ ε hτ) (qspInitProg x hx d) (fidPost x d v hv) :=
  (qspFidelityDeriv x hx d v hv E τ ε hτ).sound

end

/-! ## §9. Non-vacuity: an explicit ε-good store and input with expectation `c` -/

section Witness

variable (x : ℕ) (hx : 0 < x)

theorem zsC_false (S : Finset (SysL x)) : zsC x S (fun _ => false) = 1 :=
  Finset.prod_eq_one fun k _ => by simp

/-- The vacuum pattern is an eigenvector of the interaction Hamiltonian with
eigenvalue `0`. -/
theorem hubbard_vac_eig :
    hubbardOp x 0 1 (deltav (QubitCells (SysL x)) (qbIdx (SysL x) (fun _ => false)))
      = ((0 : ℝ) : ℂ) • deltav (QubitCells (SysL x)) (qbIdx (SysL x) (fun _ => false)) := by
  rw [hubbard_diag x (fun _ => false)]
  rw [Finset.sum_congr rfl (fun j _ => by
    rw [zsC_false, zsC_false]
    norm_num : ∀ j ∈ (univ : Finset (Fin (nPairs x))),
      (4⁻¹ : ℂ) * ((1 - zsC x (nSet x (pL x j)) (fun _ => false)) *
        (1 - zsC x (nSet x (pR x j)) (fun _ => false))) = 0)]
  simp

/-- The vacuum pattern is a unit vector. -/
theorem norm_vac : ‖deltav (QubitCells (SysL x)) (qbIdx (SysL x) (fun _ => false))‖ = 1 := by
  refine norm_eq_one_of_inner_self ?_
  have hdd := dv_dot (D := QubitCells (SysL x))
    (qbIdx (SysL x) (fun _ => false)) (qbIdx (SysL x) (fun _ => false))
  rw [hdd, if_pos rfl]

/-- The zero-angle padded sequence is zero. -/
theorem phiSeq_zero (d : ℕ) : phiSeq d (fun _ => (0 : ℝ)) = fun _ => (0 : ℝ) := by
  funext k
  rw [phiSeq]
  split_ifs <;> rfl

theorem norm_neg_one_pow_le (m : ℕ) : ‖(-1 : ℂ) ^ m‖ ≤ 1 + 0 := by
  rw [norm_pow, norm_neg, norm_one, one_pow]
  norm_num

include hx in
/-- **Non-vacuity**: at even depth `d = 2m`, zero angles, store
`(t, U) = (0, 1)` (fragment counters `0`), eigenvalue `E = 0`, target
`τ = (−1)^m` and `ε = 0`, the store is ε-good and the precondition
expectation at the intended pure input `∣0⟩_a ⊗ v` is exactly
`c = max(‖τ‖ − ε, 0)² = 1 > 0`. -/
theorem fidPre_witness (m : ℕ) :
    expectE (fidPre x (2 * m)
        (deltav (QubitCells (SysL x)) (qbIdx (SysL x) (fun _ => false))) (norm_vac x)
        0 ((-1 : ℂ) ^ m) 0 (norm_neg_one_pow_le m)).op
      ⟨(((0 : ℕ), (0 : ℕ), ((0 : ℝ), (1 : ℝ))), (fun _ => (0 : ℝ)), 0),
        PDensity.pure (sysEmb x
          (deltav (QubitCells (SysL x)) (qbIdx (SysL x) (fun _ => false))))⟩
      = 1 := by
  set v0 := deltav (QubitCells (SysL x)) (qbIdx (SysL x) (fun _ => false)) with hv0
  set σ0 : STQc (2 * m) :=
    (((0 : ℕ), (0 : ℕ), ((0 : ℝ), (1 : ℝ))), (fun _ => (0 : ℝ)), 0) with hσ0
  have hgood : goodStore x (2 * m) v0 0 ((-1 : ℂ) ^ m) 0 σ0 := by
    refine ⟨hubbard_vac_eig x, lam_zero_one_pos x hx, ?_, ?_⟩
    · rw [zero_div]
      norm_num
    · rw [zero_div, show phis (2 * m) σ0 = fun _ => (0 : ℝ) from rfl, phiSeq_zero,
        Qubitization.qspPoly_zero_even, sub_self, norm_zero]
  rw [expectE_pure,
    show (fidPre x (2 * m) v0 (norm_vac x) 0 ((-1 : ℂ) ^ m) 0
        (norm_neg_one_pow_le m)).op σ0
      = ((sysProjA x (2 * m) v0 (norm_vac x)).scaled (max (‖(-1 : ℂ) ^ m‖ - 0) 0 ^ 2)
          (cScal_nonneg ((-1 : ℂ) ^ m) 0)
          (cScal_le_one ((-1 : ℂ) ^ m) 0 (norm_neg_one_pow_le m))).op σ0 from
      Assn.mask_op_of_pos hgood,
    Assn.scaled_op,
    show (sysProjA x (2 * m) v0 (norm_vac x)).op σ0
      = sysLift (L₂ := AncL x) (outerLM v0 v0) from rfl,
    show sysEmb x v0 = ancEmbed (L₁ := SysL x) (anc0 x) v0 from rfl,
    LinearMap.smul_apply, inner_smul_right, inner_emb_sysLift, outerLM_apply,
    inner_smul_right]
  have hvv : (⟪v0, v0⟫ : ℂ) = 1 := by
    have hdd := dv_dot (D := QubitCells (SysL x))
      (qbIdx (SysL x) (fun _ => false)) (qbIdx (SysL x) (fun _ => false))
    rw [hv0, hdd, if_pos rfl]
  rw [hvv, mul_one, mul_one,
    show max (‖(-1 : ℂ) ^ m‖ - 0) 0 = 1 from by
      rw [norm_pow, norm_neg, norm_one, one_pow, sub_zero]
      exact max_eq_left zero_le_one]
  norm_num

end Witness

end Qhl.HubbardQSPSuccess

/-! ## §10. Axiom audit -/

#print axioms Qhl.HubbardQSPSuccess.qspFidelityDeriv
#print axioms Qhl.HubbardQSPSuccess.qspFidelityValid
#print axioms Qhl.HubbardQSPSuccess.fidPre_le_init
#print axioms Qhl.HubbardQSPSuccess.fidPre_witness

/-! Source derivations for the QSP fidelity triple with explicit classical hypotheses. -/
namespace Qhl.HubbardQSPSuccess.Source
open Qhl.HubbardLCU Qhl.HubbardQSP Qhl.HubbardLCUSuccess Qhl.HubbardQSPSuccess
open Qhl.BravyiKitaev Finset
open scoped ComplexInnerProductSpace ComplexOrder
variable (x : ℕ) (hx : 0 < x) (d : ℕ)

/-- PREPARE backward at an arbitrary outer-counter-insensitive postpredicate. -/
theorem prepWp (Y : Assn (STQc d) (QubitCells (WL x)))
    (hYo : ∀ σ v, Y.op ((cOuterQ d).set σ v) = Y.op σ) :
    SourceDerivTot (SourceAssertion.ofAssn (wpB6 x hx d Y) (fun _ => True))
      (prepQ x hx d) (SourceAssertion.ofAssn (wpB4 x hx d Y) (fun _ => True)) := by
  rw [prepQ_eq]
  refine .seq (B := SourceAssertion.ofAssn (wpB5 x hx d Y) (fun _ => True)) ?_ ?_
  · exact SourceDerivTot.unitary_ofAssn _ _ _ _ _ _ (fun _ h => h)
      (fun _ _ => (Reg.single _).inj) (fun _ _ => le_rfl)
  · refine .conseq (SourceAssertion.entails_refl _)
      (SourceDerivTot.countedWpChain (cOuterQ d) (HubbardLCU.NT x - 1) (fun _ => True)
        (fun σ : STQc d => prepRegE x hx σ.1) (fun σ : STQc d => prepGateE x hx σ.1)
        (prepTQ x hx d) (wpB4 x hx d Y) (fun _ _ => Iff.rfl)
        (fun k A hA σ v => prepTQ_op_set x hx d (cOuterQ d) (fun _ _ => rfl) k A hA σ v)
        (fun σ v => wpB4_op_set x hx d (cOuterQ d) (fun _ _ => rfl) (fun _ _ => rfl)
          Y hYo σ v) (fun _ _ _ => (prepReg x _).inj)
        (fun k _ σ _ hget A => by subst hget; rfl)) ?_
    exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)

/-- UNPREPARE backward at an arbitrary outer-counter-insensitive postpredicate. -/
theorem unprepWp (Y : Assn (STQc d) (QubitCells (WL x)))
    (hYo : ∀ σ v, Y.op ((cOuterQ d).set σ v) = Y.op σ) :
    SourceDerivTot (SourceAssertion.ofAssn (wpB3 x hx d Y) (fun _ => True))
      (unprepQ x hx d) (SourceAssertion.ofAssn (wpB1 x hx d Y) (fun _ => True)) := by
  rw [unprepQ_eq]
  refine .seq (B := SourceAssertion.ofAssn (wpB2 x hx d Y) (fun _ => True)) ?_ ?_
  · refine .conseq (SourceAssertion.entails_refl _)
      (SourceDerivTot.countedWpChain (cOuterQ d) (HubbardLCU.NT x - 1) (fun _ => True)
        (fun σ : STQc d => unprepRegE x hx σ.1) (fun σ : STQc d => unprepGateE x hx σ.1)
        (unprepTQ x hx d) (wpB2 x hx d Y) (fun _ _ => Iff.rfl)
        (fun k A hA σ v => unprepTQ_op_set x hx d (cOuterQ d) (fun _ _ => rfl) k A hA σ v)
        (fun σ v => wpB2_op_set x hx d (cOuterQ d) (fun _ _ => rfl) Y hYo σ v)
        (fun _ _ _ => (prepReg x _).inj)
        (fun k _ σ _ hget A => by subst hget; rfl)) ?_
    exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)
  · exact SourceDerivTot.unitary_ofAssn _ _ _ _ _ _ (fun _ h => h)
      (fun _ _ => (Reg.single _).inj) (fun _ _ => le_rfl)

/-- Source weakest-precondition preservation through a compound SELECT rung. -/
theorem selectWpStep (Y : Assn (STQc d) (QubitCells (WL x)))
    (hYi : ∀ σ v, Y.op ((cInnerQ d).set σ v) = Y.op σ) :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofFam (cOuterQ d).get
        (wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y)))
        (fun σ => True ∧ σ.1.1 < HubbardLCU.NT x))
      (((sgnBody x hx).mapStore StoreLens.fst).seq
        (countedProg (cInnerQ d) (fun _ => 2 ^ x)
          ((ctrlBody x hx).mapStore StoreLens.fst)))
      (SourceAssertion.ofAssn (Assn.ofFam (cOuterQ d).get
        (fun k => wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) (k + 1)))
        (fun σ => True ∧ σ.1.1 < HubbardLCU.NT x)) := by
  let J : ℕ → Assn (STQc d) (QubitCells (WL x)) := fun m =>
    Assn.ofFam (cOuterQ d).get fun k =>
      wpSuffix (letterTQ x hx d k) (2 ^ x)
        (wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) (k + 1)) m
  refine .seq (B := SourceAssertion.ofAssn (J 0)
    (fun σ => True ∧ σ.1.1 < HubbardLCU.NT x)) ?_ ?_
  · apply SourceDerivTot.unitary_ofAssn (fun σ : STQc d => sgnRegE x hx σ.1)
      (fun σ : STQc d => sgnGateE x hx σ.1) _ _ _ _ (fun _ h => h) (fun _ _ => (Reg.single _).inj)
    intro σ hσ
    rw [Assn.ofFam_op]
    simp only [cOuterQ, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst,
      Function.comp_apply, CounterLens.fst3]
    rw [wpSuffix_of_lt hσ.2]
    change (rungTQ x hx d σ.1.1 _).op σ ≤
      ((Assn.ofFam (cOuterQ d).get _).unitaryPre _ _).op σ
    rw [Assn.unitaryPre_ofFam_op]
    exact le_rfl
  · refine .conseq (SourceAssertion.entails_refl _)
      (SourceDerivTot.countedFamily (cInnerQ d) (2 ^ x)
        (fun σ => True ∧ σ.1.1 < HubbardLCU.NT x) J ((ctrlBody x hx).mapStore StoreLens.fst)
        (fun _ _ => Iff.rfl) ?_ ?_ ?_) ?_
    · intro m σ v
      change (wpSuffix (letterTQ x hx d σ.1.1) (2 ^ x)
        (wpSuffix (rungTQ x hx d) (HubbardLCU.NT x) (wpB3 x hx d Y) (σ.1.1 + 1)) m).op
          ((cInnerQ d).set σ v) = _
      apply wpSuffix_op_set (letterTQ x hx d σ.1.1) _ (cInnerQ d)
        (fun k A hA σ' v' => letterTQ_op_set x hx d (cInnerQ d) σ.1.1 k A hA σ' v')
      intro σ' v'
      exact wpSuffix_op_set (rungTQ x hx d) (wpB3 x hx d Y) (cInnerQ d)
        (fun k A hA τ w => rungTQ_op_set x hx d (cInnerQ d)
          (fun _ _ => rfl) k A hA τ w)
        (fun τ w => wpB3_op_set x hx d (cInnerQ d) (fun _ _ => rfl) (fun _ _ => rfl) Y hYi τ w)
        (σ.1.1 + 1) σ' v'
    · apply SourceDerivTot.unitary_ofAssn (fun σ : STQc d => ctrlRegE x hx σ.1)
        (fun σ : STQc d => ctrlGateE x hx σ.1) _ _ _ _ (fun _ h => h)
        (fun _ _ => (ctrlReg x _ _).inj)
      intro σ hσ
      simp only [J, Assn.ofFam_op, cInnerQ, CounterLens.snd3, cOuterQ, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst,
      Function.comp_apply, CounterLens.fst3]
      have hm : σ.1.2.1 < 2 ^ x := hσ.2
      rw [wpSuffix_of_lt hm]
      rw [Assn.unitaryPre_ofFam_op, Assn.unitaryPre_ofFam_op]
      exact le_rfl
    · intro z
      exact SourceDerivTot.unitary_identity (fun σ : STQc d => ctrlRegE x hx σ.1)
        (fun σ : STQc d => ctrlGateE x hx σ.1) _
        (fun _ _ => (ctrlReg x _ _).inj)
    · apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1)
      intro σ _
      simp only [J, Assn.ofFam_op, cOuterQ, CounterLens.pullbackFst,
        CounterLens.pullback, StoreLens.fst,
        Function.comp_apply, CounterLens.fst3, wpSuffix_full]
      exact le_rfl

/-- SELECT's source weakest-precondition loop. -/
theorem selectWp (Y : Assn (STQc d) (QubitCells (WL x)))
    (hYo : ∀ σ v, Y.op ((cOuterQ d).set σ v) = Y.op σ)
    (hYi : ∀ σ v, Y.op ((cInnerQ d).set σ v) = Y.op σ) :
    SourceDerivTot (SourceAssertion.ofAssn (wpB4 x hx d Y) (fun _ => True))
      (selQ x hx d) (SourceAssertion.ofAssn (wpB3 x hx d Y) (fun _ => True)) := by
  rw [selQ_eq]
  refine .conseq (SourceAssertion.entails_refl _)
    (SourceDerivTot.countedWpBody (cOuterQ d) (HubbardLCU.NT x)
      (fun _ => True) (rungTQ x hx d) (wpB3 x hx d Y) (((sgnBody x hx).mapStore StoreLens.fst).seq
        (countedProg (cInnerQ d) (fun _ => 2 ^ x)
          ((ctrlBody x hx).mapStore StoreLens.fst)))
      (fun _ _ => Iff.rfl)
      (fun k A hA σ v => rungTQ_op_set x hx d (cOuterQ d)
        (fun _ _ => rfl) k A hA σ v)
      (fun σ v => wpB3_op_set x hx d (cOuterQ d) (fun _ _ => rfl) (fun _ _ => rfl) Y hYo σ v)
      (selectWpStep x hx d Y hYi)
      (fun _ => HubbardQSP.Source.rungIdentityQ x hx d _ (fun _ _ => Iff.rfl))) ?_
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)


/-- Source weakest-precondition derivation for the full loop body. -/
theorem bodyWp (Y : Assn (STQc d) (QubitCells (WL x)))
    (hYo : ∀ σ v, Y.op ((cOuterQ d).set σ v) = Y.op σ)
    (hYi : ∀ σ v, Y.op ((cInnerQ d).set σ v) = Y.op σ) :
    SourceDerivTot (SourceAssertion.ofAssn (wpBody x hx d Y) (fun _ => True))
      (bodyProg x hx d) (SourceAssertion.ofAssn Y (fun _ => True)) := by
  refine .seq (B := SourceAssertion.ofAssn
    (Y.comp fun σ : STQc d => (σ.1, σ.2.1, σ.2.2 + 1)) (fun _ => True)) ?_
    (.assign _ (SourceAssertion.ofAssn Y (fun _ => True)))
  refine .seq (B := SourceAssertion.ofAssn (wpB6 x hx d Y) (fun _ => True)) ?_ ?_
  · exact SourceDerivTot.unitary_ofAssn _ _ _ _ _ _ (fun _ h => h)
      (fun _ _ => (Reg.single _).inj) (fun _ _ => le_rfl)
  · exact .seq (prepWp x hx d Y hYo)
      (.seq (selectWp x hx d Y hYo hYi) (.seq (unprepWp x hx d Y hYo)
        (SourceDerivTot.unitary_ofAssn _ _ _ _ _ _ (fun _ h => h)
          (fun _ _ => (Reg.single _).inj) (fun _ _ => le_rfl))))

variable (v : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) (hv : ‖v‖ = 1)

/-- The backward invariant is preserved using the source body proof. -/
theorem bodyInvariant :
    SourceDerivTot
      (SourceAssertion.ofAssn (Jw x hx d v hv) (fun σ => True ∧ gdQ d σ = true))
      (bodyProg x hx d) (SourceAssertion.ofAssn (Jw x hx d v hv) (fun _ => True)) := by
  refine .conseq ?_
    (bodyWp x hx d (Jw x hx d v hv) (fun _ _ => rfl) (fun _ _ => rfl))
    (SourceAssertion.entails_refl _)
  apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial)
  intro σ hσ
  have hlt : cnt d σ < d := by simpa [gdQ] using hσ.2
  apply le_of_eq
  rw [wpBody_op, Jw_op, Jw_op, walkRem_split x hx d σ hlt, adjoint_comp_conj]

/-- The remaining-walk loop with separate invariant and identity-rank premises. -/
theorem loop :
    SourceDerivTot (SourceAssertion.ofAssn (Jw x hx d v hv) (fun _ => True))
      (.while (gdQ d) (bodyProg x hx d))
      (SourceAssertion.ofAssn (Jw x hx d v hv) (fun σ => True ∧ gdQ d σ = false)) := by
  exact .whileLoop (gdQ d) (fun σ => (rank d σ : Int))
    (fun _ _ => Int.natCast_nonneg _) (bodyInvariant x hx d v hv)
    (Qhl.HubbardQSP.Source.bodyIdentityRank x hx d)

/-- QSP's literal counter initialization followed by its source loop. -/
theorem circuit :
    SourceDerivTot
      (SourceAssertion.ofAssn
        ((Jw x hx d v hv).comp fun σ : STQc d => (σ.1, σ.2.1, 0)) (fun _ => True))
      (qspProg x hx d) (SourceAssertion.ofAssn (fidPost x d v hv) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (.seq (.assign _ (SourceAssertion.ofAssn (Jw x hx d v hv) (fun _ => True)))
      (loop x hx d v hv)) ?_
  apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial)
  intro σ hσ
  have h := HubbardQSPSuccess.post_le x hx d v hv σ
  rw [Assn.mandNot_op_of_false hσ.2] at h
  exact h

/-- The original scaled observable and the separate full classical good-store condition. -/
noncomputable def fidelityPre (E : ℝ) (τ : ℂ) (ε : ℝ) (hτ : ‖τ‖ ≤ 1 + ε) :
    SourceAssertion (STQc d) (QubitCells (WL x)) :=
  SourceAssertion.ofAssn
    ((sysProjA x d v hv).scaled (max (‖τ‖ - ε) 0 ^ 2)
      (cScal_nonneg τ ε) (cScal_le_one τ ε hτ)) (goodStore x d v E τ ε)

/-- The exact QSP fidelity consumer is a genuine source derivation over the original
stored-coefficient, stored-angle program, including ancilla initialization. -/
theorem qspFidelityDeriv (E : ℝ) (τ : ℂ) (ε : ℝ) (hτ : ‖τ‖ ≤ 1 + ε) :
    SourceDerivTot (fidelityPre x d v hv E τ ε hτ) (qspInitProg x hx d)
      (SourceAssertion.ofAssn (fidPost x d v hv) (fun _ => True)) := by
  refine .conseq ?_
    (.seq (.initProg (fun _ => ancS x)
      (SourceAssertion.ofAssn
        ((Jw x hx d v hv).comp fun σ : STQc d => (σ.1, σ.2.1, 0)) (fun _ => True)))
      (circuit x hx d v hv)) (SourceAssertion.entails_refl _)
  apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial)
  intro σ hσ
  have h := fidPre_le_init x hx d v hv E τ ε hτ σ
  rw [fidPre, Assn.mask_op_of_pos hσ] at h
  exact h

/-- Encoding preserves the original fidelity precondition exactly. -/
theorem fidelityPre_toAssn (E : ℝ) (τ : ℂ) (ε : ℝ) (hτ : ‖τ‖ ≤ 1 + ε) :
    (fidelityPre x d v hv E τ ε hτ).toAssn = fidPre x d v hv E τ ε hτ := by
  exact SourceAssertion.toAssn_ofAssn _ _

/-- The original quantitative fidelity triple follows from the genuine source root. -/
theorem qspFidelityValid (E : ℝ) (τ : ℂ) (ε : ℝ) (hτ : ‖τ‖ ≤ 1 + ε) :
    validTot (fidPre x d v hv E τ ε hτ) (qspInitProg x hx d) (fidPost x d v hv) := by
  simpa only [fidelityPre_toAssn, SourceAssertion.toAssn_ofAssn_true] using
    (qspFidelityDeriv x hx d v hv E τ ε hτ).sound

end Qhl.HubbardQSPSuccess.Source

#print axioms Qhl.HubbardQSPSuccess.Source.bodyWp

#print axioms Qhl.HubbardQSPSuccess.Source.qspFidelityDeriv

#print axioms Qhl.HubbardQSPSuccess.Source.qspFidelityValid
