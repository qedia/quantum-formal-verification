import Qhl.Logic.Source.CountedStateChain
import Qhl.Logic.Source.ProductStateFam
import Qhl.Logic.Soundness
import Qhl.Logic.CountedStateChain
import Qhl.Logic.Frame
import Qhl.Gate.Phase
import Qhl.Register.Qubits
import Qhl.Register.BravyiKitaev
import Qhl.Register.BKSets
import Qhl.Logic.WpChain

/-!
# The Bravyi–Kitaev basis change, as a total-correctness triple

The Bravyi–Kitaev transform of Seeley–Richard–Love (arXiv:1208.5986, Fig. 2,
**ascending-index convention**: qubit `0` is the first orbital, qubit
`2^x - 1` the last) sends an occupation-number basis state `∣f⟩` of `n = 2^x`
qubits to the Bravyi–Kitaev-encoded basis state `∣β_{2^x} f⟩` (all sums
mod 2). The circuit implementing it is the **Fenwick parity network**: at
level `ℓ = 0, …, x-1` (block size `2^{ℓ+1}`), one `CNOT` per block `k` with
control `k·2^{ℓ+1} + 2^ℓ - 1` (the parity of the lower half-block,
accumulated by the previous levels) and target `k·2^{ℓ+1} + 2^{ℓ+1} - 1`
(the block's parity cell), small blocks first. The classical layer — the
matrix `β_{2^x}`, its bit-vector action `bkVec`, the network fold `netVec`,
and the agreement `netVec x x f = bkVec x f` — is
`Qhl/Register/BravyiKitaev.lean`.

The program renders the network with **all `n`-dependence in control flow**
and constant-arity gates only, as two nested genuine `while` loops over the
classical store `σT = ℕ × ℕ` (first component: the level counter `ℓ`;
second component: the rung counter `k`):

```
ℓ := 0;
while ℓ < x do
  (k := 0;
   while k < 2^x do
     if (k+1)·2^{ℓ+1} ≤ 2^x then (q_c(ℓ,k), q_t(ℓ,k)) *= CNOT;
     k := k + 1
   od);
  ℓ := ℓ + 1
od
```

The rung body reads the store on both coordinates: the guard
`(k+1)·2^{ℓ+1} ≤ 2^x` (R-Cond) selects the blocks of the current level, and
the two-cell register expression (W3) computes the `CNOT`'s
(control, target) cells from `(ℓ, k)`. The triple, generic in `x` and in
**every** input bit vector `f`,

```
⊢ₜ { ∣f⟩⟨f∣ }  bkProg x  { ∣bkVec x f⟩⟨bkVec x f∣ },
```

is derived with the basis-state invariant throughout — `CNOT`s permute basis
states, so the invariant after `ℓ` levels is the partially transformed basis
ket `∣netVec x ℓ f⟩` (`J`, read off the first store component), and the
chain state after `k` rungs of the current level is `∣levelPart x ℓ k …⟩`
(`Ac`). The **outer** loop is closed by **(R-Loop-tot)**
(`DerivTot.whileLoopSource`) with the integer cast of `x - ℓ`. Invariant
preservation is separate from identity-predicate decrease on all quantum inputs.
The **inner** loop is the counted `while` of
`Qhl/Logic/CountedWhile.lean` on the second store component with the
constant bound `2^x`, discharged by ONE call of the packaged chain rule
`DerivTot.countedStateChain_relSource` (itself built from the printed constructors
only, closed by (R-Loop-tot) with ranking function `2^x - k`), relativised
to a predicate on the outer level. The state-family and identity derivations
supply the two source premises independently; each state-family rung is ONE
`DerivTot.countedRung_ite` — the paper's (R-Cond) with (Ax-Uni)+(R-Conseq)
on the live branch and (Ax-Ski)+(R-Conseq) on the dead one. The per-rung
state algebra is the library two-cell frame bridge `regLift_pairGate_prodV`
(CoqQ `lift_lf` on a `tenvm` state) fed the gate's own fact `CNOT_vpair`.
Everything else is the proof system: (Ax-Uni), (Ax-Ski), (Ax-Ass), (R-Cond),
(R-Seq), (R-Conseq) and (R-Loop-tot); no loop is ever unfolded by induction
on the program.

The triple is genuine and non-vacuous: the endpoints are the distinct basis
kets `∣f⟩` and `∣bkVec x f⟩` (pinned to their delta forms by
`prodV_qbit_eq_deltav`), the assertions are the projector effects `∣v⟩⟨v∣`
(`Assn.ofState`), `bkValid` runs `bkDeriv` through soundness, and
`bkPre_expect_one` exhibits the pure input `∣f⟩⟨f∣` with expectation `1`.
-/

namespace Qhl.BKTransform

open Qhl Qhl.BravyiKitaev Finset
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal

section

variable (x : ℕ) (f : Fin (2 ^ x) → Bool)

/-! ## §1. The program: the Fenwick network over the store `ℕ × ℕ` -/

/-- The rung guard (R-Cond), read entirely from the store: block `σ.2`
belongs to level `σ.1` iff `(σ.2+1)·2^{σ.1+1} ≤ 2^x` — the network guard
`liveG`. -/
def bK (σ : ℕ × ℕ) : Bool := decide (liveG x σ.1 σ.2)

/-- The two-cell register expression of the rung (W3): the `CNOT`'s
(control, target) cells, computed classically from the store — the level
`σ.1` and the block `σ.2`. All `n`-dependence lives here and in the guards;
the gate itself is the constant-arity `CNOT`. -/
def regE : RegExpr (ℕ × ℕ) (QubitL (2 ^ x)) 2 :=
  fun σ => ![cellC x σ.1 σ.2, cellT x σ.1 σ.2]

/-- The bundled `CNOT` on the tuple space of the rung's register. Because
every cell of the world is a qubit, this is one and the same gate for every
store value — at a live store it is definitionally the library
`pairGate … CNOT` (`regLift_regE_of_live`). -/
noncomputable def gateE (σ : ℕ × ℕ) :
    UnitaryOp (TSpace (QubitD (2 ^ x)) (regE x σ)) :=
  euclCongrOp (piFinTwoEquiv fun _ => Bool).symm CNOT

/-- `Dist(q̄)` at a live store value: the two computed cells are distinct. -/
theorem distE_of_live {σ : ℕ × ℕ} (hlive : liveG x σ.1 σ.2) :
    Function.Injective (regE x σ) :=
  (Reg.pair (cellC x σ.1 σ.2) (cellT x σ.1 σ.2)
    (cellC_ne_cellT_of_live hlive)).inj

/-- At a live store value, the rung's cylindrical extension is the library
two-cell gate lift: register and gate collapse to `Reg.pair`/`pairGate`
(proof-irrelevant repackaging, definitional). -/
theorem regLift_regE_of_live {σ : ℕ × ℕ} (hlive : liveG x σ.1 σ.2)
    (h : Function.Injective (regE x σ)) :
    regLift ⟨regE x σ, h⟩ (gateE x σ)
      = regLift
          (Reg.pair (cellC x σ.1 σ.2) (cellT x σ.1 σ.2)
            (cellC_ne_cellT_of_live hlive))
          (pairGate (D := QubitD (2 ^ x)) (cellC x σ.1 σ.2) (cellT x σ.1 σ.2)
              (cellC_ne_cellT_of_live hlive) CNOT :
            TSpace (QubitD (2 ^ x))
                (Reg.pair (cellC x σ.1 σ.2) (cellT x σ.1 σ.2)
                  (cellC_ne_cellT_of_live hlive)).toFun →ₗ[ℂ] _) := rfl

/-- The rung: the guarded `CNOT` — `if (σ.2+1)·2^{σ.1+1} ≤ 2^x then
(q_c, q_t) *= CNOT else skip`, everything read from the store. -/
noncomputable def rung : Prog (ℕ × ℕ) (QubitD (2 ^ x)) :=
  Prog.ite (bK x) (Prog.unitary 2 (regE x) (gateE x)) Prog.skip

/-- One level of the network: the counted `while` over the rung counter
(the second store component) with the constant bound `2^x` — every block of
every level satisfies `k < 2^x`. -/
noncomputable def levelProg : Prog (ℕ × ℕ) (QubitD (2 ^ x)) :=
  countedProg (CounterLens.snd ℕ) (fun _ => 2 ^ x) (rung x)

/-- The outer loop guard `ℓ < x`. -/
def gd (σ : ℕ × ℕ) : Bool := decide (σ.1 < x)

/-- The outer loop body: one level, then `ℓ := ℓ + 1`. -/
noncomputable def body : Prog (ℕ × ℕ) (QubitD (2 ^ x)) :=
  (levelProg x).seq (Prog.assign fun σ => (σ.1 + 1, σ.2))

/-- **The Bravyi–Kitaev basis-change program**:
`ℓ := 0; while ℓ < x do (k := 0; while k < 2^x do rung; k := k+1 od);
ℓ := ℓ + 1 od`. -/
noncomputable def bkProg : Prog (ℕ × ℕ) (QubitD (2 ^ x)) :=
  (Prog.assign fun σ => (0, σ.2)).seq (Prog.while (gd x) (body x))

/-! ## §2. The interpolating basis states (indexed by the level `ℓ : ℕ`) -/

/-- The classical state at level `σ`: the input transformed by the levels
already done — the raw counter. No clamp is needed: every rung of a level
`≥ x` is dead (its guard `(k+1)·2^{ℓ+1} ≤ 2^x` fails outright), so the fold
saturates on its own after exit (`netVec_of_ge`). -/
def vAt (σ : ℕ) : Fin (2 ^ x) → Bool := netVec x σ f

/-- The classical chain state: `k` rungs of the current level applied. -/
def vMid (σ k : ℕ) : Fin (2 ^ x) → Bool := levelPart x σ k (vAt x f σ)

theorem vAt_zero : vAt x f 0 = f := rfl

theorem vAt_of_ge {σ : ℕ} (h : x ≤ σ) : vAt x f σ = bkVec x f := by
  rw [vAt, netVec_of_ge x f σ h, netVec_top]

/-- Entering the level: no rung done yet. -/
theorem vMid_zero (σ : ℕ) : vMid x f σ 0 = vAt x f σ := rfl

/-- A dead rung does not move the chain state. -/
theorem vMid_succ_dead {σ k : ℕ} (h : ¬ liveG x σ k) :
    vMid x f σ (k + 1) = vMid x f σ k := by
  rw [vMid, levelPart_succ, rungBit_of_dead h]
  rfl

/-- A live rung advances the chain state by its `CNOT`'s classical action. -/
theorem vMid_succ_live {σ k : ℕ} (h : liveG x σ k) :
    vMid x f σ (k + 1) = cnotBit (cellC x σ k) (cellT x σ k) (vMid x f σ k) := by
  rw [vMid, levelPart_succ, rungBit_of_live h]
  rfl

/-- Exiting the level: the whole level has acted, giving the next level's
entry state — the raw fold recurrence itself, so this holds at EVERY level
(no `σ < x` side condition to thread). -/
theorem vMid_top (σ : ℕ) : vMid x f σ (2 ^ x) = vAt x f (σ + 1) := by
  rw [vMid, vAt, vAt, netVec_succ]
  rfl

/-- The quantum state at level `σ`: the basis ket `∣vAt σ⟩` in product form. -/
noncomputable def ψAt (σ : ℕ) : HS (QubitD (2 ^ x)) (univ : Finset (QubitL (2 ^ x))) :=
  prodV (QubitD (2 ^ x)) fun i => qbit (vAt x f σ i)

/-- The quantum chain state: the basis ket `∣vMid σ k⟩` in product form. -/
noncomputable def ψMid (σ k : ℕ) :
    HS (QubitD (2 ^ x)) (univ : Finset (QubitL (2 ^ x))) :=
  prodV (QubitD (2 ^ x)) fun i => qbit (vMid x f σ k i)

theorem norm_ψAt (σ : ℕ) : ‖ψAt x f σ‖ = 1 :=
  norm_prodV_eq_one _ fun _ => norm_qbit _

theorem norm_ψMid (σ k : ℕ) : ‖ψMid x f σ k‖ = 1 :=
  norm_prodV_eq_one _ fun _ => norm_qbit _

/-- The input basis ket `∣f⟩` in product form. -/
noncomputable def ψIn : HS (QubitD (2 ^ x)) (univ : Finset (QubitL (2 ^ x))) :=
  prodV (QubitD (2 ^ x)) fun i => qbit (f i)

/-- The output basis ket `∣bkVec x f⟩` in product form. -/
noncomputable def ψOut : HS (QubitD (2 ^ x)) (univ : Finset (QubitL (2 ^ x))) :=
  prodV (QubitD (2 ^ x)) fun i => qbit (bkVec x f i)

theorem norm_ψIn : ‖ψIn x f‖ = 1 := norm_prodV_eq_one _ fun _ => norm_qbit _

theorem norm_ψOut : ‖ψOut x f‖ = 1 := norm_prodV_eq_one _ fun _ => norm_qbit _

/-- At level `0` the invariant state is the input ket. -/
theorem ψAt_zero : ψAt x f 0 = ψIn x f := by
  simp only [ψAt, ψIn]
  rw [vAt_zero]

/-- After exit (`ℓ ≥ x`) the invariant state is the transformed ket. -/
theorem ψAt_of_ge {σ : ℕ} (h : x ≤ σ) : ψAt x f σ = ψOut x f := by
  simp only [ψAt, ψOut]
  rw [vAt_of_ge x f h]

/-- Entering a level: the chain starts at the invariant state. -/
theorem ψMid_zero (σ : ℕ) : ψMid x f σ 0 = ψAt x f σ := rfl

/-- A dead rung does not move the chain state. -/
theorem ψMid_succ_dead {σ k : ℕ} (h : ¬ liveG x σ k) :
    ψMid x f σ (k + 1) = ψMid x f σ k := by
  simp only [ψMid]
  rw [vMid_succ_dead x f h]

/-- Exiting a level: the next invariant state. -/
theorem ψMid_top (σ : ℕ) : ψMid x f σ (2 ^ x) = ψAt x f (σ + 1) := by
  simp only [ψMid, ψAt]
  rw [vMid_top x f σ]

/-! ## §3. The gate computations: one `CNOT` advances the chain -/

/-- **The rung action**: the lifted `CNOT` of a live rung advances the basis
chain state one step — the library two-cell frame bridge
`regLift_pairGate_prodV` (CoqQ `lift_lf` on a `tenvm` state, the vector form
of `RV_Frame`) fed the gate's own fact `CNOT_vpair`
(`∣a⟩⊗∣b⟩ ↦ ∣a⟩⊗∣a ⊕ b⟩`), plus the one-line check that updating the target
factor is the classical `cnotBit`. -/
theorem K_step {σ k : ℕ} (hlive : liveG x σ k) :
    regLift (Reg.pair (cellC x σ k) (cellT x σ k) (cellC_ne_cellT_of_live hlive))
        (pairGate (D := QubitD (2 ^ x)) (cellC x σ k) (cellT x σ k) (cellC_ne_cellT_of_live hlive)
            CNOT :
          TSpace (QubitD (2 ^ x))
              (Reg.pair (cellC x σ k) (cellT x σ k)
                (cellC_ne_cellT_of_live hlive)).toFun →ₗ[ℂ] _)
        (ψMid x f σ k)
      = ψMid x f σ (k + 1) := by
  have h := regLift_pairGate_prodV (cellC x σ k) (cellT x σ k)
    (cellC_ne_cellT_of_live hlive) CNOT (fun i => qbit (vMid x f σ k i))
    (CNOT_vpair (vMid x f σ k (cellC x σ k)) (vMid x f σ k (cellT x σ k)))
  refine h.trans ?_
  rw [ψMid, vMid_succ_live x f hlive]
  refine prodV_congr _ fun i _ => ?_
  rcases eq_or_ne i (cellT x σ k) with rfl | hit
  · rw [Function.update_self, cnotBit, Function.update_self]
  · rw [Function.update_of_ne hit, cnotBit, Function.update_of_ne hit]
    rcases eq_or_ne i (cellC x σ k) with rfl | hic
    · rw [Function.update_self]
    · rw [Function.update_of_ne hic]

/-! ## §4. The assertions, the loop invariant, and the chain family -/

/-- The outer loop invariant: "the register is in the basis ket
`∣vAt ℓ⟩`" — the input transformed by the levels already done, the level
read off the first store component. -/
noncomputable def J : Assn (ℕ × ℕ) (QubitD (2 ^ x)) :=
  Assn.ofStateFam (fun σ => ψAt x f σ.1) fun σ => norm_ψAt x f σ.1

@[simp] theorem J_op (σ : ℕ × ℕ) :
    (J x f).op σ = outerLM (ψAt x f σ.1) (ψAt x f σ.1) := rfl

/-- The stage-`k` assertion of the level chain: "the register is in the
basis ket `∣vMid ℓ k⟩`", the level read off the first store component — the
state family the counted chain rule consumes. -/
noncomputable def Ac (k : ℕ) : Assn (ℕ × ℕ) (QubitD (2 ^ x)) :=
  Assn.ofStateFam (fun σ => ψMid x f σ.1 k) fun σ => norm_ψMid x f σ.1 k

@[simp] theorem Ac_op (k : ℕ) (σ : ℕ × ℕ) :
    (Ac x f k).op σ = outerLM (ψMid x f σ.1 k) (ψMid x f σ.1 k) := rfl

/-- The precondition "the register is in the basis ket `∣f⟩`". -/
noncomputable def Pin : Assn (ℕ × ℕ) (QubitD (2 ^ x)) :=
  Assn.ofState (ψIn x f) (norm_ψIn x f)

/-- The postcondition "the register is in the basis ket `∣bkVec x f⟩`". -/
noncomputable def Qout : Assn (ℕ × ℕ) (QubitD (2 ^ x)) :=
  Assn.ofState (ψOut x f) (norm_ψOut x f)

/-- The ranking function of the outer (R-Loop-tot): the number of levels
still to do. -/
def rank (σ : ℕ × ℕ) : ℕ := x - σ.1

/-! ## §5. The rung: one `DerivTot.countedRung_ite` — (R-Cond) with
(Ax-Uni)/(Ax-Ski) -/

/-- One rung of the counted level chain, under the outer level pin
`rank = r₀ ∧ ℓ < x` and the inner counter pin `k`: the packaged conditional
rung rule — (R-Cond) (`DerivTot.cond'`), the live branch
(Ax-Uni)+(R-Conseq) closed by `K_step`, the dead branch (Ax-Ski)+(R-Conseq)
closed by `ψMid_succ_dead`. -/
theorem rungDeriv (r₀ k : ℕ) :
    DerivTot
      ((Ac x f k).mask fun σ =>
        (rank x σ = r₀ ∧ σ.1 < x) ∧ σ.2 = k ∧ k < 2 ^ x)
      (rung x)
      ((Ac x f (k + 1)).mask fun σ =>
        (rank x σ = r₀ ∧ σ.1 < x) ∧ σ.2 = k ∧ k < 2 ^ x) :=
  DerivTot.countedRung_ite (bK x) (regE x) (gateE x)
    (fun σ => norm_ψMid x f σ.1 k) (fun σ => norm_ψMid x f σ.1 (k + 1))
    (fun σ hσ hb => by
      obtain ⟨-, hk, -⟩ := hσ
      subst hk
      have hlive : liveG x σ.1 σ.2 := of_decide_eq_true hb
      refine ⟨distE_of_live x hlive, ?_⟩
      rw [regLift_regE_of_live x hlive]
      exact K_step x f hlive)
    (fun σ hσ hb => by
      obtain ⟨-, hk, -⟩ := hσ
      subst hk
      exact (ψMid_succ_dead x f (of_decide_eq_false hb)).symm)

/-! ## §6. The level chain, the outer loop body, and the outer loop -/

/-- A conditional CNOT preserves every classical identity mask: distinctness
is required only in its live branch. -/
theorem rungIdentityDeriv (φ : ℕ × ℕ → Prop) :
    DerivTot ((Assn.one : Assn (ℕ × ℕ) (QubitD (2 ^ x))).mask φ)
      (rung x) (Assn.one.mask φ) := by
  apply DerivTot.cond'
  · exact DerivTot.conseq (Assn.le_refl' _)
      (DerivTot.unitary_identity_mask _ _ (fun σ hσ =>
        distE_of_live x (of_decide_eq_true hσ.2)))
      (Assn.mask_le_mask (fun _ h => h.1) (fun _ _ => le_rfl))
  · exact DerivTot.conseq
      (Assn.mask_le_mask (fun _ h => h.1) (fun _ _ => le_rfl))
      (DerivTot.skip _) (Assn.le_refl' _)

/-- The source-derived inner loop preserves the quantum-state chain under
any predicate on the outer level counter. -/
theorem levelDeriv_mask (φ : ℕ → Prop) :
    DerivTot ((J x f).mask fun σ => φ σ.1) (levelProg x)
      ((Ac x f (2 ^ x)).mask fun σ => φ σ.1) :=
  DerivTot.countedStateChain_relSource (CounterLens.snd ℕ) (2 ^ x)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k σ => ψMid x f σ.1 k) (fun k σ => norm_ψMid x f σ.1 k)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (DerivTot.countedRung_ite (bK x) (regE x) (gateE x)
      (fun σ => norm_ψMid x f σ.1 σ.2)
      (fun σ => norm_ψMid x f σ.1 (σ.2 + 1))
      (fun σ _ hb => by
        have hlive : liveG x σ.1 σ.2 := of_decide_eq_true hb
        refine ⟨distE_of_live x hlive, ?_⟩
        rw [regLift_regE_of_live x hlive]
        exact K_step x f hlive)
      (fun _ _ hb => (ψMid_succ_dead x f (of_decide_eq_false hb)).symm))
    (fun _ => rungIdentityDeriv x _)

/-- The same inner loop independently preserves the identity predicate on
all quantum inputs under every outer-counter predicate. -/
theorem levelIdentityDeriv (φ : ℕ → Prop) :
    DerivTot ((Assn.one : Assn (ℕ × ℕ) (QubitD (2 ^ x))).mask fun σ => φ σ.1)
      (levelProg x) (Assn.one.mask fun σ => φ σ.1) :=
  DerivTot.countedIdentitySource (CounterLens.snd ℕ) (n := 2 ^ x)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (rungIdentityDeriv x _) (fun _ => rungIdentityDeriv x _)

/-- One whole level in ONE call of the relativised counted chain rule: the
inner counted `while` on the second store component, bound `2^x`, along the
chain family `Ac`, relativised to the outer level pin — the frame predicate
reads only the first component, so counter insensitivity and the bound pin
are definitional. -/
theorem levelDeriv (r₀ : ℕ) :
    DerivTot ((J x f).mask fun σ => rank x σ = r₀ ∧ σ.1 < x)
      (levelProg x)
      ((Ac x f (2 ^ x)).mask fun σ => rank x σ = r₀ ∧ σ.1 < x) :=
  levelDeriv_mask x f (fun i => x - i = r₀ ∧ i < x)

/-- Entering the outer loop body: the invariant under the guard entails the
chain entry, masked to the level pin (the guard is exactly `ℓ < x`). -/
theorem frontPremise (r₀ : ℕ) :
    (((J x f).mand (gd x)).mask fun σ => rank x σ = r₀)
      ≤ (J x f).mask fun σ => rank x σ = r₀ ∧ σ.1 < x :=
  le_of_le_of_eq
    (Assn.mand_mask_le (J x f) (gd x) fun σ => rank x σ = r₀)
    (Assn.mask_congr fun σ => by simp [gd, and_comm])

/-- The level exit entails the next invariant, under the pin: `ψMid_top`
(the level completes the next `netVec` stage) plus the rank decrease. -/
theorem endPremise (r₀ : ℕ) :
    ((Ac x f (2 ^ x)).mask fun σ => rank x σ = r₀ ∧ σ.1 < x)
      ≤ ((J x f).mask fun σ => rank x σ < r₀).comp fun σ => (σ.1 + 1, σ.2) := by
  intro σ
  by_cases hm : rank x σ = r₀ ∧ σ.1 < x
  · obtain ⟨hr, hσ⟩ := hm
    have hlt : rank x (σ.1 + 1, σ.2) < r₀ := by
      simp only [rank] at hr ⊢
      omega
    refine le_of_eq ?_
    rw [Assn.mask_op_of_pos (A := Ac x f (2 ^ x))
        (φ := fun σ => rank x σ = r₀ ∧ σ.1 < x) (σ := σ) ⟨hr, hσ⟩,
      Assn.comp_op,
      Assn.mask_op_of_pos (A := J x f)
        (φ := fun σ => rank x σ < r₀) (σ := (σ.1 + 1, σ.2)) hlt,
      Ac_op, J_op, ψMid_top x f σ.1]
  · exact Assn.op_zero_le (Assn.mask_op_of_neg
      (A := Ac x f (2 ^ x))
      (φ := fun σ => rank x σ = r₀ ∧ σ.1 < x) (σ := σ) hm)

/-- The outer loop body at ranking value `r₀`: the level chain glued to
`ℓ := ℓ + 1` by (R-Seq), with (R-Conseq) at both ends. -/
theorem bodyDeriv (r₀ : ℕ) :
    DerivTot (((J x f).mand (gd x)).mask fun σ => rank x σ = r₀)
      (body x)
      ((J x f).mask fun σ => rank x σ < r₀) :=
  DerivTot.seq
    (DerivTot.conseq (frontPremise x f r₀) (levelDeriv x f r₀)
      (endPremise x f r₀))
    (DerivTot.assign (fun σ => (σ.1 + 1, σ.2))
      ((J x f).mask fun σ => rank x σ < r₀))

/-- The source loop rule's separate invariant-preservation premise. -/
theorem bodyInvariantDeriv :
    DerivTot ((J x f).mand (gd x)) (body x) (J x f) := by
  apply DerivTot.seq _ (DerivTot.assign (fun σ => (σ.1 + 1, σ.2)) _)
  apply DerivTot.conseq _ (levelDeriv_mask x f (fun i => i < x)) _
  · intro σ
    by_cases hg : gd x σ = true
    · have hk : σ.1 < x := by simpa [gd] using hg
      rw [Assn.mand_op_of_true hg, Assn.mask_op_of_pos (φ := fun τ => τ.1 < x) (σ := σ) hk]
    · exact Assn.op_zero_le (Assn.mand_op_of_false (by simpa using hg))
  · apply Assn.mask_le_of_imp_le
    intro σ _
    refine le_of_eq ?_
    rw [Assn.comp_op, Ac_op, J_op, ψMid_top]

/-- The source loop rule's independent identity-predicate decrease premise. -/
theorem bodyIdentityRankDeriv (z : ℤ) :
    DerivTot ((Assn.one : Assn (ℕ × ℕ) (QubitD (2 ^ x))).mask fun σ =>
        True ∧ gd x σ = true ∧ (rank x σ : ℤ) = z)
      (body x) (Assn.one.mask fun σ => (rank x σ : ℤ) < z) := by
  refine DerivTot.seq
    (levelIdentityDeriv x (fun i =>
      True ∧ decide (i < x) = true ∧ (↑(x - i) : ℤ) = z)) ?_
  apply DerivTot.conseq _ (DerivTot.assign (fun σ => (σ.1 + 1, σ.2)) _)
    (Assn.le_refl' _)
  apply Assn.mask_le_of_imp_le
  intro σ hσ
  have hk : σ.1 < x := of_decide_eq_true hσ.2.1
  have hr : (↑(x - σ.1) : ℤ) = z := hσ.2.2
  refine Assn.le_op_of_eq_one ?_
  rw [Assn.comp_op, Assn.mask_op_of_pos (φ := fun σ => (rank x σ : ℤ) < z) ?_,
    Assn.one_op]
  change (↑(x - (σ.1 + 1)) : ℤ) < z
  omega

/-- **(R-Loop-tot)**: the invariant `J` with ranking function
`rank (ℓ, k) = x - ℓ` — DEFINITE termination, no meta-level rule. -/
theorem loopDeriv :
    DerivTot (J x f) (Prog.while (gd x) (body x)) ((J x f).mandNot (gd x)) := by
  have hm : (J x f).mask (fun _ => True) = J x f := by
    ext σ
    simp
  have h := DerivTot.whileLoopSource (A := J x f) (φ := fun _ => True)
    (fun σ => (rank x σ : ℤ)) (fun _ _ => Int.natCast_nonneg _)
    (by simpa only [hm] using bodyInvariantDeriv x f) (bodyIdentityRankDeriv x)
  simpa only [hm] using h

theorem pre_le : Pin x f ≤ (J x f).comp fun σ => (0, σ.2) := by
  intro σ
  refine le_of_eq ?_
  show outerLM (ψIn x f) (ψIn x f) = outerLM (ψAt x f 0) (ψAt x f 0)
  rw [ψAt_zero]

theorem post_le : (J x f).mandNot (gd x) ≤ Qout x f := by
  intro σ
  by_cases hg : gd x σ = true
  · exact Assn.op_zero_le
      (Assn.mandNot_op_of_true (A := J x f) (b := gd x) (σ := σ) hg)
  · have hσ : x ≤ σ.1 := by simpa [gd] using hg
    refine le_of_eq ?_
    rw [Assn.mandNot_op_of_false (A := J x f) (b := gd x) (σ := σ)
        (by simpa using hg),
      J_op, Qout, Assn.ofState_op, ψAt_of_ge x f hσ]

/-! ## §7. The triple and soundness -/

/-- **The Bravyi–Kitaev triple**
`{ ∣f⟩⟨f∣ } bkProg x { ∣bkVec x f⟩⟨bkVec x f∣ }` is derivable in `QHL⁺_tot`,
generic in `x` (`n = 2^x` qubits) and in every input bit vector `f`: the
Fenwick `CNOT` network implements exactly the basis change `β_{2^x}` of
arXiv:1208.5986 (ascending-index convention), both loops genuine `while`
loops closed by (R-Loop-tot) — the outer with ranking function `x - ℓ`, the
inner (inside `countedStateChain_relSource`) with ranking function `2^x - k`. -/
theorem bkDeriv : DerivTot (Pin x f) (bkProg x) (Qout x f) :=
  DerivTot.conseq (pre_le x f)
    (DerivTot.seq (DerivTot.assign (fun σ => (0, σ.2)) (J x f)) (loopDeriv x f))
    (post_le x f)

/-- **The semantic content**, through soundness (L-4): for every input
density operator, the expectation of `∣f⟩⟨f∣` bounds the terminal expectation
of `∣bkVec x f⟩⟨bkVec x f∣` — all the mass of a register in `∣f⟩` terminates,
in `∣bkVec x f⟩`. -/
theorem bkValid : validTot (Pin x f) (bkProg x) (Qout x f) :=
  (bkDeriv x f).sound

/-! ## §8. Non-vacuity: the endpoints are genuine basis kets -/

/-- A product of `qbit` factors is the computational basis ket of its bit
vector (library `prodV_single`, CoqQ `t2tv_tuple`): the endpoints are honest
deltas. -/
theorem prodV_qbit_eq_deltav (v : Fin (2 ^ x) → Bool) :
    prodV (QubitD (2 ^ x)) (W := (univ : Finset (QubitL (2 ^ x))))
        (fun i => qbit (v i))
      = deltav (QubitD (2 ^ x)) fun i => v (i : QubitL (2 ^ x)) :=
  prodV_single (QubitD (2 ^ x)) _

/-- A concrete input the precondition accepts with all of its mass: the pure
basis state `∣f⟩⟨f∣` at store `(0, 0)`. -/
noncomputable def inputState : CQState (ℕ × ℕ) (QubitD (2 ^ x)) :=
  ⟨(0, 0), ⟨outerLM (ψIn x f) (ψIn x f), isPositive_outerLM_self _⟩⟩

/-- **The precondition is satisfiable**: it has expectation `1` — the full
mass — in the concrete pure basis input, so the triple is not vacuous. -/
theorem bkPre_expect_one : expectE (Pin x f).op (inputState x f) = 1 := by
  have hin : (⟪ψIn x f, ψIn x f⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_ψIn]
    norm_num
  rw [expectE, expect,
    show (inputState x f).q.op = outerLM (ψIn x f) (ψIn x f) from rfl,
    show (Pin x f).op (inputState x f).cls = outerLM (ψIn x f) (ψIn x f) from rfl,
    trace_outerLM_comp, outerLM_apply, inner_smul_right, hin]
  simp

end

end Qhl.BKTransform

#print axioms Qhl.BKTransform.bkDeriv
#print axioms Qhl.BKTransform.bkValid
#print axioms Qhl.BKTransform.bkPre_expect_one
#print axioms Qhl.BravyiKitaev.netVec_top
#print axioms Qhl.BravyiKitaev.bkMat_inv_succ

/-! The original Bravyi--Kitaev circuit through source conditional and counted-loop rules. -/
namespace Qhl.BKTransform
open Finset BravyiKitaev
variable (x : ℕ) (f : Fin (2 ^ x) → Bool)

theorem rungIdentitySource (φ : ℕ × ℕ → Prop) :
    SourceDerivTot (SourceAssertion.identity (D := QubitD (2 ^ x)) φ)
      (rung x) (SourceAssertion.identity φ) := by
  apply SourceDerivTot.cond
  · refine .conseq (SourceAssertion.entails_refl _)
      (SourceDerivTot.unitary_identity (regE x) (gateE x) _
        (fun σ h => distE_of_live x (of_decide_eq_true h.2))) ?_
    exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1) (fun _ _ => le_rfl)
  · refine .conseq ?_ (.skip _) (SourceAssertion.entails_refl _)
    exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1) (fun _ _ => le_rfl)

theorem levelIdentitySource (φ : ℕ → Prop) :
    SourceDerivTot
      (SourceAssertion.identity (D := QubitD (2 ^ x)) (fun σ => φ σ.1))
      (levelProg x) (SourceAssertion.identity (fun σ => φ σ.1)) := by
  apply SourceDerivTot.countedIdentity (CounterLens.snd ℕ) (fun _ => 2 ^ x)
    (fun σ => φ σ.1) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
  · exact rungIdentitySource x _
  · intro z; exact rungIdentitySource x _

theorem levelSourceDeriv (φ : ℕ → Prop) :
    SourceDerivTot (SourceAssertion.ofAssn (J x f) (fun σ => φ σ.1))
      (levelProg x)
      (SourceAssertion.ofAssn
        (Assn.ofStateFam (fun σ : ℕ × ℕ => ψAt x f (σ.1 + 1))
          (fun σ => norm_ψAt x f (σ.1 + 1))) (fun σ => φ σ.1)) := by
  apply SourceDerivTot.countedStateChainVar (CounterLens.snd ℕ) (fun _ => 2 ^ x)
    (fun σ => φ σ.1) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k σ => ψMid x f σ.1 k) (fun k σ => norm_ψMid x f σ.1 k)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun σ _ => ψMid_top x f σ.1)
  · apply SourceDerivTot.cond
    · refine .conseq (SourceAssertion.entails_refl _)
        (SourceDerivTot.countedRung_fam (regE x) (gateE x)
          (fun σ => norm_ψMid x f σ.1 σ.2)
          (fun σ => norm_ψMid x f σ.1 (σ.2 + 1)) ?_) ?_
      · intro σ hσ
        have hlive : liveG x σ.1 σ.2 := of_decide_eq_true hσ.2
        refine ⟨distE_of_live x hlive, ?_⟩
        rw [regLift_regE_of_live x hlive]
        exact K_step x f hlive
      · exact SourceAssertion.entails_ofAssn _ _ _ _
          (fun _ h => h.1) (fun _ _ => le_rfl)
    · refine .conseq ?_ (.skip _) (SourceAssertion.entails_refl _)
      apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1)
      intro σ hσ
      change outerLM (ψMid x f σ.1 σ.2) (ψMid x f σ.1 σ.2) ≤
        outerLM (ψMid x f σ.1 (σ.2 + 1)) (ψMid x f σ.1 (σ.2 + 1))
      exact le_of_eq (by
        simp only [ψMid_succ_dead x f (of_decide_eq_false hσ.2)])
  · intro z
    exact rungIdentitySource x _

/-- Exact original program and basis-state specification; both loops use source rules. -/
theorem bkSourceDeriv :
    SourceDerivTot (SourceAssertion.ofAssn (Pin x f) (fun _ => True)) (bkProg x)
      (SourceAssertion.ofAssn (Qout x f) (fun _ => True)) := by
  apply SourceDerivTot.countedStateChainVar (CounterLens.fst ℕ) (fun _ => x)
    (fun _ => True) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k _ => ψAt x f k) (fun k _ => norm_ψAt x f k)
    (hv₀ := fun _ => norm_ψIn x f) (hv₁ := fun _ => norm_ψOut x f)
    (fun _ _ _ => rfl) (fun _ _ => ψAt_zero x f)
    (fun _ _ => ψAt_of_ge x f (Nat.le_refl x))
  · exact levelSourceDeriv x f (fun i => True ∧ i < x)
  · intro z
    exact levelIdentitySource x (fun i => True ∧ i < x ∧ (↑(x - i) : Int) = z)

theorem bkSourceValid : validTot (Pin x f) (bkProg x) (Qout x f) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (bkSourceDeriv x f).sound

end Qhl.BKTransform

#print axioms Qhl.BKTransform.bkSourceDeriv
#print axioms Qhl.BKTransform.bkSourceValid


/-! Coherent correctness for every normalized input, with the original program. -/
namespace Qhl.BKTransform
open Finset BravyiKitaev

noncomputable def rungOp (x l k : ℕ) : EndM (QubitD (2 ^ x)) univ :=
  if h : liveG x l k then
    regLift ⟨regE x (l,k), distE_of_live x h⟩ (gateE x (l,k)) else 1

noncomputable def midOp (x l : ℕ) : ℕ → EndM (QubitD (2 ^ x)) univ
  | 0 => 1
  | k + 1 => rungOp x l k ∘ₗ midOp x l k

noncomputable def levelOp (x l : ℕ) := midOp x l (2 ^ x)
noncomputable def atOp (x : ℕ) : ℕ → EndM (QubitD (2 ^ x)) univ
  | 0 => 1
  | l + 1 => levelOp x l ∘ₗ atOp x l
noncomputable def bkCircuitOp (x : ℕ) := atOp x x

theorem rungOp_unitary (x l k : ℕ) : IsUnitary (rungOp x l k) := by
  unfold rungOp
  split
  · exact isUnitary_regLift _ _
  · exact isUnitary_one

theorem midOp_unitary (x l k : ℕ) : IsUnitary (midOp x l k) := by
  induction k with
  | zero => exact isUnitary_one
  | succ k ih => exact (rungOp_unitary x l k).comp ih

theorem atOp_unitary (x l : ℕ) : IsUnitary (atOp x l) := by
  induction l with
  | zero => exact isUnitary_one
  | succ l ih => exact (midOp_unitary x l (2 ^ x)).comp ih

def basisBitsEquiv (x : ℕ) :
    (↥(univ : Finset (QubitL (2 ^ x))) → Bool) ≃ (Fin (2 ^ x) → Bool) where
  toFun f i := f ⟨i, mem_univ i⟩
  invFun f i := f i.val
  left_inv _ := rfl
  right_inv _ := rfl

/-- The independent BK basis permutation. -/
noncomputable def bkUnitary (x : ℕ) : UnitaryOp (HS (QubitD (2 ^ x)) univ) :=
  permOp ((basisBitsEquiv x).trans ((bkEquiv x).trans (basisBitsEquiv x).symm))

theorem bkUnitary_basis (x : ℕ) (f : Fin (2 ^ x) → Bool) :
    (bkUnitary x : EndM (QubitD (2 ^ x)) univ) (ψIn x f) = ψOut x f := by
  change (bkUnitary x : EndM (QubitD (2 ^ x)) univ)
    (prodV (QubitD (2 ^ x)) (fun i => qbit (f i))) =
    prodV (QubitD (2 ^ x)) (fun i => qbit (bkVec x f i))
  rw [prodV_qbit_eq_deltav, prodV_qbit_eq_deltav]
  exact permOp_single _ _ _

theorem rungOp_step (x : ℕ) (f : Fin (2 ^ x) → Bool) (l k : ℕ) :
    rungOp x l k (ψMid x f l k) = ψMid x f l (k + 1) := by
  unfold rungOp
  split
  · rename_i h
    rw [regLift_regE_of_live x h]
    exact K_step x f h
  · rename_i h
    exact (ψMid_succ_dead x f h).symm

theorem midOp_basis (x : ℕ) (f : Fin (2 ^ x) → Bool) (l k : ℕ) :
    midOp x l k (ψAt x f l) = ψMid x f l k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [midOp, LinearMap.comp_apply, ih, rungOp_step]

theorem atOp_basis (x : ℕ) (f : Fin (2 ^ x) → Bool) (l : ℕ) :
    atOp x l (ψIn x f) = ψAt x f l := by
  induction l with
  | zero => exact (ψAt_zero x f).symm
  | succ l ih => rw [atOp, LinearMap.comp_apply, ih, levelOp, midOp_basis, ψMid_top]

theorem bkCircuitOp_eq_bkUnitary (x : ℕ) :
    bkCircuitOp x = (bkUnitary x : EndM (QubitD (2 ^ x)) univ) := by
  apply linM_ext (QubitD (2 ^ x))
  intro f
  have h := atOp_basis x (fun i => f ⟨i, mem_univ i⟩) x
  rw [ψAt_of_ge x _ (Nat.le_refl x)] at h
  rw [bkCircuitOp, ← prodV_qbit_eq_deltav x (fun i => f ⟨i, mem_univ i⟩)]
  exact h.trans (bkUnitary_basis x _).symm

end Qhl.BKTransform

namespace Qhl.BKTransform
open Finset BravyiKitaev
variable (x : ℕ) (ψ : HS (QubitD (2 ^ x)) univ) (hψ : ‖ψ‖ = 1)

noncomputable def coherentAt (l : ℕ) := atOp x l ψ
noncomputable def coherentMid (l k : ℕ) := midOp x l k (coherentAt x ψ l)
include hψ in
theorem norm_coherentAt (l : ℕ) : ‖coherentAt x ψ l‖ = 1 :=
  norm_eq_one_of_isUnitary (atOp_unitary x l) hψ
include hψ in
theorem norm_coherentMid (l k : ℕ) : ‖coherentMid x ψ l k‖ = 1 :=
  norm_eq_one_of_isUnitary (midOp_unitary x l k) (norm_coherentAt x ψ hψ l)

theorem coherent_levelSource (φ : ℕ → Prop) :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : ℕ × ℕ => coherentAt x ψ σ.1)
        (fun σ => norm_coherentAt x ψ hψ σ.1)) (fun σ => φ σ.1))
      (levelProg x)
      (SourceAssertion.ofAssn (Assn.ofStateFam (fun σ : ℕ × ℕ => coherentAt x ψ (σ.1 + 1))
        (fun σ => norm_coherentAt x ψ hψ (σ.1 + 1))) (fun σ => φ σ.1)) := by
  apply SourceDerivTot.countedStateChainVar (CounterLens.snd ℕ) (fun _ => 2 ^ x)
    (fun σ => φ σ.1) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k σ => coherentMid x ψ σ.1 k) (fun k σ => norm_coherentMid x ψ hψ σ.1 k)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  · apply SourceDerivTot.cond
    · refine .conseq (SourceAssertion.entails_refl _)
        (SourceDerivTot.countedRung_fam (regE x) (gateE x)
          (fun σ => norm_coherentMid x ψ hψ σ.1 σ.2)
          (fun σ => norm_coherentMid x ψ hψ σ.1 (σ.2 + 1)) ?_) ?_
      · intro σ hσ
        have hlive : liveG x σ.1 σ.2 := of_decide_eq_true hσ.2
        refine ⟨distE_of_live x hlive, ?_⟩
        change _ = rungOp x σ.1 σ.2 (coherentMid x ψ σ.1 σ.2)
        rw [rungOp, dif_pos hlive]
      · exact SourceAssertion.entails_ofAssn _ _ _ _
          (fun _ h => h.1) (fun _ _ => le_rfl)
    · refine .conseq ?_ (.skip _) (SourceAssertion.entails_refl _)
      apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1)
      intro σ hσ
      have hdead : ¬ liveG x σ.1 σ.2 := of_decide_eq_false hσ.2
      have heq : coherentMid x ψ σ.1 (σ.2 + 1) = coherentMid x ψ σ.1 σ.2 := by
        simp only [coherentMid, midOp, LinearMap.comp_apply, rungOp, dif_neg hdead,
          Module.End.one_apply]
      change outerLM (coherentMid x ψ σ.1 σ.2) (coherentMid x ψ σ.1 σ.2) ≤
        outerLM (coherentMid x ψ σ.1 (σ.2 + 1)) (coherentMid x ψ σ.1 (σ.2 + 1))
      rw [heq]
  · intro z
    exact rungIdentitySource x _

/-- Source total correctness on every normalized coherent input. -/
theorem bkCoherentSourceDeriv :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofState ψ hψ) (fun _ : ℕ × ℕ => True)) (bkProg x)
      (SourceAssertion.ofAssn
        (Assn.ofState ((bkUnitary x : EndM (QubitD (2 ^ x)) univ) ψ)
          (norm_eq_one_of_isUnitary (bkUnitary x).isUnitary hψ)) (fun _ => True)) := by
  apply SourceDerivTot.countedStateChainVar (CounterLens.fst ℕ) (fun _ => x)
    (fun _ => True) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k _ => coherentAt x ψ k) (fun k _ => norm_coherentAt x ψ hψ k)
    (hv₀ := fun _ => hψ)
    (hv₁ := fun _ => norm_eq_one_of_isUnitary (bkUnitary x).isUnitary hψ)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => congrArg (fun A : EndM (QubitD (2 ^ x)) univ => A ψ)
      (bkCircuitOp_eq_bkUnitary x))
  · exact coherent_levelSource x ψ hψ (fun i => True ∧ i < x)
  · intro z
    exact levelIdentitySource x (fun i => True ∧ i < x ∧ (↑(x - i) : Int) = z)

theorem bkCoherentSourceValid :
    validTot (Assn.ofState ψ hψ) (bkProg x)
      (Assn.ofState ((bkUnitary x : EndM (QubitD (2 ^ x)) univ) ψ)
        (norm_eq_one_of_isUnitary (bkUnitary x).isUnitary hψ)) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (bkCoherentSourceDeriv x ψ hψ).sound
end Qhl.BKTransform

#print axioms Qhl.BKTransform.bkCircuitOp_eq_bkUnitary
#print axioms Qhl.BKTransform.bkCoherentSourceDeriv
#print axioms Qhl.BKTransform.bkCoherentSourceValid

namespace Qhl.BKTransform
open Finset

theorem midOp_eq_chainOp_range (x l k : ℕ) :
    midOp x l k = chainOp (List.range k) (rungOp x l) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [midOp, List.range_succ, chainOp_concat, ih]

theorem atOp_eq_chainOp_range (x l : ℕ) :
    atOp x l = chainOp (List.range l) (levelOp x) := by
  induction l with
  | zero => rfl
  | succ l ih => rw [atOp, List.range_succ, chainOp_concat, ih]
end Qhl.BKTransform
