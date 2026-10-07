import Qhl.Logic.Source.StateApproximation
import Qhl.Logic.Soundness
import Qhl.Logic.CountedStateChain
import Qhl.Register.TFIMApprox
import Qhl.Logic.Approximation

/-!
# Trotterized simulation of the transverse-field Ising model, as a
# total-correctness triple

The Hamiltonian-simulation task for the `n`-qubit **transverse-field Ising
model**

```
H  =  H_X + H_ZZ,      H_X = Σ_{j<n} a j · X_j,      H_ZZ = Σ_{j<n-1} b j · Z_j Z_{j+1},
```

by the **first-order Trotter product formula** (Lloyd, *Universal quantum
simulators*, Science 273 (1996); Nielsen–Chuang §4.7; Lin, *Lecture notes on
quantum algorithms for scientific computation*, arXiv:2201.08309 §3): split
the evolution time `θ` into `N` equal slices and realise each slice by one
elementary rotation per Hamiltonian term.  **Every loop is a genuine `while`
loop** — the printed proof system has no `for` rule, so each rotation layer is
the counted shape `cnt := 0 ; while cnt < B do BODY ; cnt := cnt + 1 od`
(`countedProg`, `Qhl/Logic/CountedWhile.lean`):

```
i := 0;
while i < N do
  (j := 0; while j < n   do  q_j          *= Rx  (2·(a j)·θ/N); j := j+1 od);
  (j := 0; while j < n-1 do  (q_j, q_j+1) *= Rzz (2·(b j)·θ/N); j := j+1 od);
  i := i + 1
od
```

over the classical store `σT = ℕ × ℕ` — `σ.1` the slice counter, `σ.2` the
layer counter, reused by both layers of a slice — on the standard `n`-qubit
world.  The registers are genuine store-dependent register expressions
(`RegExpr`, the paper's `q̄(t̄)`), reading the touched cell `cell n σ.2` off
the layer counter (`Qhl/Register/Qubits.lean`); totality of the register
expressions forces `[NeZero n]`, and off the loop masks the coupling gate is
`1` (those stores are unreachable under the masks).  Unlike the diagonal Ising
model (`Qhl/Examples/TrotterIsingTriple.lean`), here `H_X` and `H_ZZ` do
**need not** commute. The exact implementation of the product formula is
proved first as an intermediate statement: for an arbitrary `n`-qubit unit
ket `ψ` the derived triple is

```
{ ∣ψ⟩⟨ψ∣ }  tfimProg  { ∣W(θ/N)^N ψ⟩⟨W(θ/N)^N ψ∣ },      W(φ) = B(φ) ∘ A(φ),
```

where `A(φ) = AOp φ = e^{-iφ H_X}` and `B(φ) = BOp φ = e^{-iφ H_ZZ}` are the
two slice layers (`Qhl/Register/TFIM.lean`), exactly as the circuit computes
them.  The two **layer characterizations** proved there — `AOp_pmState` (the
`X` layer is diagonal on the `±` product basis with spectrum
`E_X(s) = Σ_j (a j)·z(s j)`) and `BOp_deltav` (the `ZZ` layer is the diagonal
phase of `E_ZZ(y) = Σ_j (b j)·z(y_j)z(y_{j+1})` on the computational basis) —
justify reading `W(θ/N)^N` as `(e^{-i(θ/N)H_ZZ} e^{-i(θ/N)H_X})^N`, the
first-order product formula for `e^{-iθH}` — and the **closed-form finals**
`tfimDerivExp`/`tfimValidExp` (§7b) make that reading a theorem: their
postcondition is literally `(e^{-i(θ/N)·HZZ} e^{-i(θ/N)·HX})^N ∣ψ⟩`, stated
against the independently defined Hamiltonians `HX = Σ_j (a j)·X_j`,
`HZZ = Σ_j (b j)·Z_jZ_{j+1}` and the operator exponential `expOp`
(`Qhl/HSpace/OperatorExp.lean`), through the operator equalities
`AOp_eq_expOp`/`BOp_eq_expOp` (`Qhl/Register/TFIM.lean` §5) and one more
(R-Conseq).  The finals require **`N ≥ 1`**
(`[NeZero N]`): the slice angle is `θ/N`, and `N = 0` has no intended Trotter
interpretation (Lean's totalized division would make the term well-typed but
meaningless).

The approximation theorem `tfimDerivApprox` (§8) additionally compares the
program with the target evolution `expOp (-iθ • (HX + HZZ))`. For an error
tolerance ε at least `θ²/(2N) ‖[HX,HZZ]‖`, it derives the normalized effects
`|ψ⟩⟨ψ|/(1+ε)` and `(|Uθψ⟩⟨Uθψ|+εI)/(1+ε)`. The finite-step operator-norm
bound and the sharp projector comparison are proved in reusable library
modules. Scaling the existing constructor derivation and applying (R-Conseq)
retains validity for every input density operator. The limit as N tends to
infinity is not a separate theorem here.

**How each loop is closed.** The outer loop uses `DerivTot.whileLoopSource`
with separate invariant preservation and identity-predicate decrease. Its
integer rank is the cast of `N − σ.1`, nonnegative everywhere. The invariant
is the raw family `sW` masked by `i ≤ N`, so the exit counter is exactly `N`.
Each rotation layer uses `DerivTot.countedStateChain_relSource` along the
store-indexed families `chi1` and `chi2`, under any predicate on the slice
counter. The invariant derivation carries the outer guard through these
layers. The independent identity derivation preserves the outer guard and
integer rank equality on all quantum inputs, before the assignment decreases
the rank. Each layer separately supplies a state-family gate step and an
identity-mask gate step, with distinctness on its inner guard. The gate actions
are `chi1_succ` and `chi2_succ`; the endpoint equation is `chi2_top`.

-/

namespace Qhl.TrotterTFIM

open Qhl Finset
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal

section

variable (n N : ℕ) [NeZero n] (θ : ℝ) (ca : Fin n → ℝ) (cb : Fin (n - 1) → ℝ)
variable (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1)

/-! ## §1. The program: `N` Trotter slices, one rotation per Hamiltonian term

The store is `σT = ℕ × ℕ`: `σ.1` is the slice counter, `σ.2` the layer
counter (reused by the two layers of a slice, each re-initialising it). -/

/-- The one-cell register expression of the `Rx` gate: the cell the layer
counter names. -/
def xReg : RegExpr (ℕ × ℕ) (QubitL n) 1 := fun σ => (Reg.single (cell n σ.2)).toFun

/-- The slice gate of the transverse-field term `a j · X_j` at the layer
counter: `Rx(2·(a j)·θ/N) = e^{-i((a j)θ/N)X}`, on the tuple space of its
register. -/
noncomputable def xGateE (σ : ℕ × ℕ) : UnitaryOp (TSpace (QubitD n) (xReg n σ)) :=
  singleGate (QubitD n) (cell n σ.2) (Rx (2 * ca (cell n σ.2) * (θ / (N : ℝ))))

/-- The two-cell register expression of the `Rzz` gate: the coupling
`(q_j, q_{j+1})` the layer counter names. -/
def zzReg : RegExpr (ℕ × ℕ) (QubitL n) 2 := fun σ => ![cell n σ.2, cell n (σ.2 + 1)]

/-- The paper's `Dist(q̄)` (eq (2)) for the coupling register, where the layer
counter is below the coupling count. -/
theorem zzCells_ne {σ : ℕ × ℕ} (h : σ.2 < n - 1) : cell n σ.2 ≠ cell n (σ.2 + 1) :=
  cell_ne n (by omega) (by omega) (by omega)

/-- The slice gate of the coupling term `b j · Z_j Z_{j+1}` at the layer
counter: `Rzz(2·(b j)·θ/N) = e^{-i((b j)θ/N)Z⊗Z}`, on the tuple space of its
register; `1` where the register expression degenerates (off the loop masks
only). -/
noncomputable def zzGateE (σ : ℕ × ℕ) : UnitaryOp (TSpace (QubitD n) (zzReg n σ)) :=
  if h : σ.2 < n - 1 then
    pairGate (D := QubitD n) (cell n σ.2) (cell n (σ.2 + 1)) (zzCells_ne n h)
      (Rzz (2 * cb ⟨σ.2, h⟩ * (θ / (N : ℝ))))
  else 1

/-- The `Rx` layer of one slice, as a counted `while` on the layer counter:
`j := 0; while j < n do q_j *= Rx(2·(a j)·θ/N); j := j+1 od` — one slice of
`e^{-i(θ/N)H_X}`. -/
noncomputable def xLayer : Prog (ℕ × ℕ) (QubitD n) :=
  countedProg (.snd ℕ) (fun _ => n) (.unitary 1 (xReg n) (xGateE n N θ ca))

/-- The `Rzz` layer of one slice, as a counted `while` on the layer counter:
`j := 0; while j < n-1 do (q_j, q_{j+1}) *= Rzz(2·(b j)·θ/N); j := j+1 od` —
one slice of `e^{-i(θ/N)H_ZZ}`. -/
noncomputable def zzLayer : Prog (ℕ × ℕ) (QubitD n) :=
  countedProg (.snd ℕ) (fun _ => n - 1) (.unitary 2 (zzReg n) (zzGateE n N θ cb))

/-- One first-order Trotter slice: one rotation per Hamiltonian term.  The two
layers do not commute — their order is part of the product formula. -/
noncomputable def slice : Prog (ℕ × ℕ) (QubitD n) := (xLayer n N θ ca).seq (zzLayer n N θ cb)

/-- The outer loop guard `i < N`. -/
def gd (σ : ℕ × ℕ) : Bool := decide (σ.1 < N)

/-- The outer loop body: one slice, then `i := i + 1`. -/
noncomputable def body : Prog (ℕ × ℕ) (QubitD n) :=
  (slice n N θ ca cb).seq (Prog.assign fun σ => (σ.1 + 1, σ.2))

/-- The program `i := 0; while i < N do slice; i := i + 1 od`. -/
noncomputable def tfimProg : Prog (ℕ × ℕ) (QubitD n) :=
  (Prog.assign fun σ => (0, σ.2)).seq (Prog.while (gd N) (body n N θ ca cb))

/-! ## §2. The interpolating states -/

/-- The loop-invariant state after `s` slices: `W(θ/N)^s ∣ψ⟩`, at the **raw**
slice counter — the counter bound `s ≤ N` is carried by the invariant's mask
(§4), not by a saturation of the family (the house mask pattern of the
counted-while layer). -/
noncomputable def sW (s : ℕ) : HS (QubitD n) (univ : Finset (QubitL n)) :=
  wIter n ca cb (θ / (N : ℝ)) ψ s

/-- The chain state at stage `k` of the `Rx` layer of slice `s+1`: the first
`k` gates of the `X` layer applied to the invariant state. -/
noncomputable def chi1 (s k : ℕ) : HS (QubitD n) (univ : Finset (QubitL n)) :=
  aPart n ca (θ / (N : ℝ)) k (sW n N θ ca cb ψ s)

/-- The chain state at stage `k` of the `Rzz` layer: the first `k` couplings
applied after the whole `X` layer. -/
noncomputable def chi2 (s k : ℕ) : HS (QubitD n) (univ : Finset (QubitL n)) :=
  bPart n cb (θ / (N : ℝ)) k (AOp n ca (θ / (N : ℝ)) (sW n N θ ca cb ψ s))

omit [NeZero n] in
include hψ in
theorem norm_sW (s : ℕ) : ‖sW n N θ ca cb ψ s‖ = 1 :=
  norm_wIter n ca cb _ hψ _

omit [NeZero n] in
include hψ in
theorem norm_chi1 (s k : ℕ) : ‖chi1 n N θ ca cb ψ s k‖ = 1 :=
  norm_eq_one_of_isUnitary (isUnitary_aPart n ca _ k) (norm_sW n N θ ca cb ψ hψ s)

omit [NeZero n] in
include hψ in
theorem norm_chi2 (s k : ℕ) : ‖chi2 n N θ ca cb ψ s k‖ = 1 :=
  norm_eq_one_of_isUnitary (isUnitary_bPart n cb _ k)
    (norm_eq_one_of_isUnitary (isUnitary_AOp n ca _) (norm_sW n N θ ca cb ψ hψ s))

omit [NeZero n] in
/-- Stage `0` of the `Rx` layer is the invariant state. -/
theorem chi1_zero (s : ℕ) : chi1 n N θ ca cb ψ s 0 = sW n N θ ca cb ψ s := by
  simp only [chi1, aPart_zero, Module.End.one_apply]

omit [NeZero n] in
/-- The exit of the `Rx` layer is the entry of the `Rzz` layer: both are the
whole `X` layer applied. -/
theorem chi1_top (s : ℕ) : chi1 n N θ ca cb ψ s n = chi2 n N θ ca cb ψ s 0 := by
  simp only [chi1, chi2, AOp, bPart_zero, Module.End.one_apply]

/-! ## §3. The gate computations: one rung per slice gate -/

omit [NeZero n] in
/-- **The `Rx` rung**: gate `i` of the `X` layer advances the chain one stage
— the definitional unfolding `aPart (i+1) = xGate i ∘ aPart i`. -/
theorem chi1_succ (s : ℕ) (i : Fin n) :
    xGate n ca (θ / (N : ℝ)) i (chi1 n N θ ca cb ψ s (i : ℕ))
      = chi1 n N θ ca cb ψ s ((i : ℕ) + 1) := by
  simp only [chi1]
  rw [aPart_succ_of_lt n ca (θ / (N : ℝ)) i.isLt, LinearMap.comp_apply]

omit [NeZero n] in
/-- **The `Rzz` rung**: coupling gate `j` of the `ZZ` layer advances the
chain one stage — the definitional unfolding `bPart (j+1) = zzGate j ∘ bPart j`. -/
theorem chi2_succ (s : ℕ) (j : Fin (n - 1)) :
    zzGate n cb (θ / (N : ℝ)) j (chi2 n N θ ca cb ψ s (j : ℕ))
      = chi2 n N θ ca cb ψ s ((j : ℕ) + 1) := by
  simp only [chi2]
  rw [bPart_succ_of_lt n cb (θ / (N : ℝ)) j.isLt, LinearMap.comp_apply]

omit [NeZero n] in
/-- **The slice closes**: the exit of the `Rzz` layer is the invariant state
of the next slice — `W`-composition itself, `W^{s+1}ψ = W (W^s ψ)`.  No
spectral computation: the slice operator is by definition the composite of
its layers. -/
theorem chi2_top (s : ℕ) :
    chi2 n N θ ca cb ψ s (n - 1) = sW n N θ ca cb ψ (s + 1) := by
  simp only [chi2, sW]
  rw [wIter_succ]
  rfl

omit [NeZero n] in
/-- At `s = 0` no slice has acted: the state is `∣ψ⟩`. -/
theorem sW_zero : sW n N θ ca cb ψ 0 = ψ := by
  simp only [sW]
  rw [wIter_zero]

omit [NeZero n] in
/-- At `s = N` the accumulated state is the full product-formula state
`W(θ/N)^N ∣ψ⟩`. -/
theorem sW_top : sW n N θ ca cb ψ N = wIter n ca cb (θ / (N : ℝ)) ψ N := rfl

/-! ## §4. The assertions: the outer loop invariant and the layer endpoints

All are store-indexed pure-state projector families (`Assn.ofStateFam`),
reading only the slice counter `σ.1`; the outer invariant `J` is the raw
family `Jfam` masked by the counter bound `i ≤ N` (the house mask pattern —
the family is total in the counter, the bound is a mask). -/

include hψ in
/-- The raw invariant family: "the register is in `W(θ/N)^i ∣ψ⟩`", read at
the raw slice counter. -/
noncomputable def Jfam : Assn (ℕ × ℕ) (QubitD n) :=
  Assn.ofStateFam (fun σ => sW n N θ ca cb ψ σ.1)
    (fun σ => norm_sW n N θ ca cb ψ hψ σ.1)

omit [NeZero n] in
@[simp] theorem Jfam_op (σ : ℕ × ℕ) :
    (Jfam n N θ ca cb ψ hψ).op σ
      = outerLM (sW n N θ ca cb ψ σ.1) (sW n N θ ca cb ψ σ.1) := rfl

include hψ in
/-- The outer loop invariant: the raw family under the counter-bound mask —
"`i ≤ N`, and the register is in `W(θ/N)^i ∣ψ⟩`". -/
noncomputable def J : Assn (ℕ × ℕ) (QubitD n) :=
  (Jfam n N θ ca cb ψ hψ).mask fun σ => σ.1 ≤ N

omit [NeZero n] in
/-- Under the counter bound the invariant reads the raw family. -/
theorem J_op_of_le {σ : ℕ × ℕ} (h : σ.1 ≤ N) :
    (J n N θ ca cb ψ hψ).op σ
      = outerLM (sW n N θ ca cb ψ σ.1) (sW n N θ ca cb ψ σ.1) := by
  simp only [J]
  rw [Assn.mask_op_of_pos (A := Jfam n N θ ca cb ψ hψ)
    (φ := fun σ => σ.1 ≤ N) (σ := σ) h, Jfam_op]

include hψ in
/-- The mid-slice assertion: the whole `X` layer applied (exit of the `Rx`
chain, entry of the `Rzz` chain). -/
noncomputable def Amid : Assn (ℕ × ℕ) (QubitD n) :=
  Assn.ofStateFam (fun σ => chi2 n N θ ca cb ψ σ.1 0)
    (fun σ => norm_chi2 n N θ ca cb ψ hψ σ.1 0)

include hψ in
/-- The slice-exit assertion: the next invariant state, pre-increment. -/
noncomputable def Astep : Assn (ℕ × ℕ) (QubitD n) :=
  Assn.ofStateFam (fun σ => sW n N θ ca cb ψ (σ.1 + 1))
    (fun σ => norm_sW n N θ ca cb ψ hψ (σ.1 + 1))

include hψ in
/-- The precondition "the register is in `∣ψ⟩`". -/
noncomputable def Ppre : Assn (ℕ × ℕ) (QubitD n) := Assn.ofState ψ hψ

include hψ in
/-- The postcondition "the register is in `∣W(θ/N)^N ψ⟩` — the state the
first-order product formula prepares after `N` slices". -/
noncomputable def Qpost : Assn (ℕ × ℕ) (QubitD n) :=
  Assn.ofState (wIter n ca cb (θ / (N : ℝ)) ψ N) (norm_wIter n ca cb _ hψ N)

/-- The ranking function of (R-Loop-tot): the number of slices still to do. -/
def rank (σ : ℕ × ℕ) : ℕ := N - σ.1

/-- The frame predicate carrying the outer guard-and-rank mask through the
inner counted loops.  It reads only the slice counter `σ.1`, so it is
invariant under layer-counter writes definitionally. -/
abbrev slicePin (r₀ : ℕ) (σ : ℕ × ℕ) : Prop := σ.1 < N ∧ rank N σ = r₀

/-! ## §5. The layer chains: one relativised counted-chain call each -/

include hψ in
/-- The `Rx` layer: **one** `DerivTot.countedStateChain_relSource` call on the layer
counter, along the store-indexed family `fun k σ => chi1 σ.1 k`; each gate
pass is one `DerivTot.countedRung_fam` whose datum is `chi1_succ`. -/
theorem xChainDeriv_mask (φ : ℕ → Prop) :
    DerivTot
      ((Jfam n N θ ca cb ψ hψ).mask (fun σ => φ σ.1))
      (xLayer n N θ ca)
      ((Amid n N θ ca cb ψ hψ).mask (fun σ => φ σ.1)) :=
  DerivTot.countedStateChain_relSource (CounterLens.snd ℕ) n
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k σ => chi1 n N θ ca cb ψ σ.1 k)
    (fun k σ => norm_chi1 n N θ ca cb ψ hψ σ.1 k)
    (fun _ _ _ => rfl)
    (fun σ _ => chi1_zero n N θ ca cb ψ σ.1)
    (fun σ _ => chi1_top n N θ ca cb ψ σ.1)
    (DerivTot.countedRung_fam (xReg n) (xGateE n N θ ca)
      (fun σ => norm_chi1 n N θ ca cb ψ hψ σ.1 σ.2)
      (fun σ => norm_chi1 n N θ ca cb ψ hψ σ.1 (σ.2 + 1))
      (fun σ hσ => by
        have hk : σ.2 < n := hσ.2
        refine ⟨fun a b _ => Subsingleton.elim a b, ?_⟩
        show xGate n ca (θ / (N : ℝ)) (cell n σ.2) (chi1 n N θ ca cb ψ σ.1 σ.2)
            = chi1 n N θ ca cb ψ σ.1 (σ.2 + 1)
        rw [show cell n σ.2 = ⟨σ.2, hk⟩ from cell_eq_mk n hk]
        exact chi1_succ n N θ ca cb ψ σ.1 ⟨σ.2, hk⟩))
    (fun _ => DerivTot.unitary_identity_mask _ _
      (fun _ _ _ _ _ => Subsingleton.elim _ _))

include hψ in
/-- The `Rzz` layer: **one** `DerivTot.countedStateChain_relSource` call on the
(re-initialised) layer counter, along `fun k σ => chi2 σ.1 k`; the exit
identity is `chi2_top` — `W`-composition, using the `σ.1 < N` the frame
predicate carries. -/
theorem zzChainDeriv_mask (φ : ℕ → Prop) :
    DerivTot
      ((Amid n N θ ca cb ψ hψ).mask (fun σ => φ σ.1))
      (zzLayer n N θ cb)
      ((Astep n N θ ca cb ψ hψ).mask (fun σ => φ σ.1)) :=
  DerivTot.countedStateChain_relSource (CounterLens.snd ℕ) (n - 1)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k σ => chi2 n N θ ca cb ψ σ.1 k)
    (fun k σ => norm_chi2 n N θ ca cb ψ hψ σ.1 k)
    (fun _ _ _ => rfl)
    (fun _ _ => rfl)
    (fun σ _ => chi2_top n N θ ca cb ψ σ.1)
    (DerivTot.countedRung_fam (zzReg n) (zzGateE n N θ cb)
      (fun σ => norm_chi2 n N θ ca cb ψ hψ σ.1 σ.2)
      (fun σ => norm_chi2 n N θ ca cb ψ hψ σ.1 (σ.2 + 1))
      (fun σ hσ => by
        have hk : σ.2 < n - 1 := hσ.2
        have hlt : σ.2 < n - 1 := hk
        have hne : cell n σ.2 ≠ cell n (σ.2 + 1) := zzCells_ne n hlt
        refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
        show regLift (Reg.pair (cell n σ.2) (cell n (σ.2 + 1)) hne)
            (zzGateE n N θ cb σ) (chi2 n N θ ca cb ψ σ.1 σ.2)
            = chi2 n N θ ca cb ψ σ.1 (σ.2 + 1)
        rw [show zzGateE n N θ cb σ
            = pairGate (D := QubitD n) (cell n σ.2) (cell n (σ.2 + 1)) hne
                (Rzz (2 * cb ⟨σ.2, hk⟩ * (θ / (N : ℝ)))) from by
              simp only [zzGateE]
              rw [dif_pos hlt],
          zzLift_eq n cb (θ / (N : ℝ)) ⟨σ.2, hk⟩ hne
            (Fin.ext (cell_val n (by omega)))
            (Fin.ext (cell_val n (by omega)))]
        exact chi2_succ n N θ ca cb ψ σ.1 ⟨σ.2, hk⟩))
    (fun k => DerivTot.unitary_identity_mask _ _ (fun σ hσ =>
      (Reg.pair _ _ (zzCells_ne n (by
        have he : σ.2 = k := hσ.2.1
        have hk : k < n - 1 := hσ.2.2
        omega))).inj))

include hψ in
theorem xChainDeriv (r₀ : ℕ) :
    DerivTot ((Jfam n N θ ca cb ψ hψ).mask (slicePin N r₀))
      (xLayer n N θ ca) ((Amid n N θ ca cb ψ hψ).mask (slicePin N r₀)) :=
  xChainDeriv_mask n N θ ca cb ψ hψ (fun i => i < N ∧ N - i = r₀)

include hψ in
theorem zzChainDeriv (r₀ : ℕ) :
    DerivTot ((Amid n N θ ca cb ψ hψ).mask (slicePin N r₀))
      (zzLayer n N θ cb) ((Astep n N θ ca cb ψ hψ).mask (slicePin N r₀)) :=
  zzChainDeriv_mask n N θ ca cb ψ hψ (fun i => i < N ∧ N - i = r₀)

include hψ in
/-- One whole slice: the two layer chains glued by (R-Seq) — the mid-slice
assertion is shared literally. -/
theorem sliceDeriv (r₀ : ℕ) :
    DerivTot
      ((Jfam n N θ ca cb ψ hψ).mask (slicePin N r₀))
      (slice n N θ ca cb)
      ((Astep n N θ ca cb ψ hψ).mask (slicePin N r₀)) :=
  DerivTot.seq (xChainDeriv n N θ ca cb ψ hψ r₀) (zzChainDeriv n N θ ca cb ψ hψ r₀)

/-! ## §6. The outer loop body: the (R-Loop-tot) step obligations -/

omit [NeZero n] in
include hψ in
/-- Entering the slice at ranking value `r₀`: the masked invariant entails the
chain entry under the frame predicate — the guard `i < N` discharges the
invariant's counter-bound mask. -/
theorem front_le (r₀ : ℕ) :
    ((J n N θ ca cb ψ hψ).mand (gd N)).mask (fun σ => rank N σ = r₀)
      ≤ (Jfam n N θ ca cb ψ hψ).mask (slicePin N r₀) := by
  intro σ
  by_cases hm : rank N σ = r₀
  · by_cases hg : gd N σ = true
    · have hσ1 : σ.1 < N := by simpa [gd] using hg
      refine le_of_eq ?_
      rw [Assn.mask_op_of_pos (A := (J n N θ ca cb ψ hψ).mand (gd N))
          (φ := fun σ => rank N σ = r₀) (σ := σ) hm,
        Assn.mand_op_of_true (A := J n N θ ca cb ψ hψ) (b := gd N) (σ := σ) hg,
        J_op_of_le n N θ ca cb ψ hψ hσ1.le,
        Assn.mask_op_of_pos (A := Jfam n N θ ca cb ψ hψ)
          (φ := slicePin N r₀) (σ := σ) ⟨hσ1, hm⟩, Jfam_op]
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := (J n N θ ca cb ψ hψ).mand (gd N))
        (φ := fun σ => rank N σ = r₀) (σ := σ) hm]
      exact Assn.mand_op_of_false (A := J n N θ ca cb ψ hψ) (b := gd N) (σ := σ)
        (by simpa using hg)
  · exact Assn.op_zero_le (Assn.mask_op_of_neg
      (A := (J n N θ ca cb ψ hψ).mand (gd N))
      (φ := fun σ => rank N σ = r₀) (σ := σ) hm)

omit [NeZero n] in
include hψ in
/-- Leaving the slice at ranking value `r₀`: the chain exit entails the
(Ax-Ass) precondition of `i := i + 1`, with the rank strictly decreased. -/
theorem back_le (r₀ : ℕ) :
    (Astep n N θ ca cb ψ hψ).mask (slicePin N r₀)
      ≤ ((J n N θ ca cb ψ hψ).mask fun σ => rank N σ < r₀).comp
          fun σ => (σ.1 + 1, σ.2) := by
  intro σ
  by_cases hp : slicePin N r₀ σ
  · have hlt : rank N (σ.1 + 1, σ.2) < r₀ := by
      obtain ⟨h1, h2⟩ := hp
      simp only [rank] at h2 ⊢
      omega
    have hle : (σ.1 + 1, σ.2).1 ≤ N := Nat.succ_le_of_lt hp.1
    refine le_of_eq ?_
    rw [Assn.mask_op_of_pos (A := Astep n N θ ca cb ψ hψ)
        (φ := slicePin N r₀) (σ := σ) hp,
      Assn.comp_op,
      Assn.mask_op_of_pos (A := J n N θ ca cb ψ hψ)
        (φ := fun σ => rank N σ < r₀) (σ := (σ.1 + 1, σ.2)) hlt,
      J_op_of_le n N θ ca cb ψ hψ hle]
    rfl
  · exact Assn.op_zero_le (Assn.mask_op_of_neg
      (A := Astep n N θ ca cb ψ hψ) (φ := slicePin N r₀) (σ := σ) hp)

include hψ in
/-- The loop body at ranking value `r₀`: the slice (two chained layers) glued
to `i := i + 1` by (R-Seq), with (R-Conseq) at both ends. -/
theorem bodyDeriv (r₀ : ℕ) :
    DerivTot
      (((J n N θ ca cb ψ hψ).mand (gd N)).mask fun σ => rank N σ = r₀)
      (body n N θ ca cb)
      ((J n N θ ca cb ψ hψ).mask fun σ => rank N σ < r₀) :=
  DerivTot.seq
    (DerivTot.conseq (front_le n N θ ca cb ψ hψ r₀)
      (sliceDeriv n N θ ca cb ψ hψ r₀)
      (back_le n N θ ca cb ψ hψ r₀))
    (DerivTot.assign (fun σ => (σ.1 + 1, σ.2))
      ((J n N θ ca cb ψ hψ).mask fun σ => rank N σ < r₀))

/-- The two rotation layers preserve every predicate on the slice counter,
independently of their quantum-state family. Both inner loops use the source rule. -/
theorem sliceIdentityDeriv (φ : ℕ → Prop) :
    DerivTot ((Assn.one : Assn (ℕ × ℕ) (QubitD n)).mask fun σ => φ σ.1)
      (slice n N θ ca cb) (Assn.one.mask fun σ => φ σ.1) := by
  apply DerivTot.seq (B := Assn.one.mask fun σ => φ σ.1)
  · exact DerivTot.countedIdentitySource (CounterLens.snd ℕ) (n := n)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
      (DerivTot.unitary_identity_mask _ _ (fun _ _ _ _ _ => Subsingleton.elim _ _))
      (fun _ => DerivTot.unitary_identity_mask _ _
        (fun _ _ _ _ _ => Subsingleton.elim _ _))
  · apply DerivTot.countedIdentitySource (CounterLens.snd ℕ) (n := n - 1)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    · exact DerivTot.unitary_identity_mask _ _ (fun σ hσ =>
        (Reg.pair _ _ (zzCells_ne n hσ.2)).inj)
    · intro k
      exact DerivTot.unitary_identity_mask _ _ (fun σ hσ =>
        (Reg.pair _ _ (zzCells_ne n (by
          have he : σ.2 = k := hσ.2.1
          have hk : k < n - 1 := hσ.2.2
          omega))).inj)

include hψ in
/-- The source rule's invariant-preservation premise, with no rank equality
in the quantum-state derivation. -/
theorem bodyInvariantDeriv :
    DerivTot ((J n N θ ca cb ψ hψ).mand (gd N))
      (body n N θ ca cb) (J n N θ ca cb ψ hψ) := by
  apply DerivTot.seq _ (DerivTot.assign (fun σ => (σ.1 + 1, σ.2)) _)
  apply DerivTot.conseq _
    (DerivTot.seq (xChainDeriv_mask n N θ ca cb ψ hψ (fun i => i < N))
      (zzChainDeriv_mask n N θ ca cb ψ hψ (fun i => i < N))) _
  · intro σ
    by_cases hg : gd N σ = true
    · have hk : σ.1 < N := by simpa [gd] using hg
      refine le_of_eq ?_
      rw [Assn.mand_op_of_true hg, J_op_of_le n N θ ca cb ψ hψ hk.le,
        Assn.mask_op_of_pos (φ := fun τ => τ.1 < N) (σ := σ) hk, Jfam_op]
    · exact Assn.op_zero_le (Assn.mand_op_of_false (by simpa using hg))
  · apply Assn.mask_le_of_imp_le
    intro σ hσ
    refine le_of_eq ?_
    rw [Assn.comp_op, J_op_of_le n N θ ca cb ψ hψ (Nat.succ_le_of_lt hσ)]
    rfl

/-- Identity-predicate decrease uses the source-derived identity derivation
of the slice, then the outer-counter assignment. -/
theorem bodyIdentityRankDeriv (z : ℤ) :
    DerivTot ((Assn.one : Assn (ℕ × ℕ) (QubitD n)).mask fun σ =>
        True ∧ gd N σ = true ∧ (rank N σ : ℤ) = z)
      (body n N θ ca cb)
      (Assn.one.mask fun σ => (rank N σ : ℤ) < z) := by
  refine DerivTot.seq
    (sliceIdentityDeriv n N θ ca cb (fun i =>
      True ∧ decide (i < N) = true ∧ (↑(N - i) : ℤ) = z)) ?_
  apply DerivTot.conseq _ (DerivTot.assign (fun σ => (σ.1 + 1, σ.2)) _)
    (Assn.le_refl' _)
  apply Assn.mask_le_of_imp_le
  intro σ hσ
  have hk : σ.1 < N := of_decide_eq_true hσ.2.1
  have hr : (↑(N - σ.1) : ℤ) = z := hσ.2.2
  refine Assn.le_op_of_eq_one ?_
  rw [Assn.comp_op, Assn.mask_op_of_pos (φ := fun σ => (rank N σ : ℤ) < z) ?_,
    Assn.one_op]
  change (↑(N - (σ.1 + 1)) : ℤ) < z
  omega

/-! ## §7. The loop, the triple, and soundness -/

include hψ in
/-- **(R-Loop-tot)**: the invariant `J` with ranking function
`rank σ = N − σ.1`, cast to the integers, with separate invariant
preservation and identity-predicate decrease. -/
theorem loopDeriv :
    DerivTot (J n N θ ca cb ψ hψ)
      (Prog.while (gd N) (body n N θ ca cb))
      ((J n N θ ca cb ψ hψ).mandNot (gd N)) := by
  have hm : (J n N θ ca cb ψ hψ).mask (fun _ => True) = J n N θ ca cb ψ hψ := by
    ext σ
    simp
  have h := DerivTot.whileLoopSource (A := J n N θ ca cb ψ hψ) (φ := fun _ => True)
    (fun σ => (rank N σ : ℤ)) (fun _ _ => Int.natCast_nonneg _)
    (by simpa only [hm] using bodyInvariantDeriv n N θ ca cb ψ hψ)
    (bodyIdentityRankDeriv n N θ ca cb)
  simpa only [hm] using h

omit [NeZero n] in
theorem pre_le : Ppre n ψ hψ ≤ (J n N θ ca cb ψ hψ).comp fun σ => (0, σ.2) := by
  intro σ
  refine le_of_eq ?_
  have h0 : (J n N θ ca cb ψ hψ).op (0, σ.2)
      = outerLM (sW n N θ ca cb ψ 0) (sW n N θ ca cb ψ 0) :=
    J_op_of_le n N θ ca cb ψ hψ (Nat.zero_le N)
  show outerLM ψ ψ = (J n N θ ca cb ψ hψ).op (0, σ.2)
  rw [h0, sW_zero]

omit [NeZero n] in
/-- At the loop exit the guard fails, so the mask pins the counter to
exactly `N`: above `N` the masked invariant is `0`, at `N` it is the
product-formula state. -/
theorem post_le : (J n N θ ca cb ψ hψ).mandNot (gd N) ≤ Qpost n N θ ca cb ψ hψ := by
  intro σ
  by_cases hg : gd N σ = true
  · exact Assn.op_zero_le
      (Assn.mandNot_op_of_true (A := J n N θ ca cb ψ hψ) (b := gd N) (σ := σ) hg)
  · have hσ : N ≤ σ.1 := by simpa [gd] using hg
    by_cases hle : σ.1 ≤ N
    · refine le_of_eq ?_
      rw [Assn.mandNot_op_of_false (A := J n N θ ca cb ψ hψ) (b := gd N) (σ := σ)
          (by simpa using hg),
        J_op_of_le n N θ ca cb ψ hψ hle, Qpost, Assn.ofState_op,
        Nat.le_antisymm hle hσ, sW_top]
    · refine Assn.op_zero_le ?_
      rw [Assn.mandNot_op_of_false (A := J n N θ ca cb ψ hψ) (b := gd N) (σ := σ)
          (by simpa using hg)]
      simp only [J]
      exact Assn.mask_op_of_neg hle

/- The slice count is at least `1`: `N = 0` has no intended Trotter
interpretation — the gates read the slice angle `θ/N`, and Lean's totalized
division would make the `N = 0` statement well-typed but meaningless as a
product-formula step.  Included in the finals `tfimDeriv`/`tfimValid`;
nothing downstream consumes an `N`-free form. -/
variable [hN : NeZero N]

-- `hN` is an interpretive requirement of the STATEMENT (it makes `θ/N` a
-- genuine slice angle); the derivation itself never has to read it, so the
-- unused-section-variable lint is silenced for this one declaration.
set_option linter.unusedSectionVars false in
include hN in
/-- **The transverse-field Ising product-formula triple**
`{ ∣ψ⟩⟨ψ∣ } tfimProg { ∣W(θ/N)^N ψ⟩⟨W(θ/N)^N ψ∣ }` is derivable in
`QHL⁺_tot`: the program implements exactly `N` slices of the first-order
Trotter product formula `W(θ/N) = e^{-i(θ/N)H_ZZ} e^{-i(θ/N)H_X}`, every loop
a counted `while` closed by (R-Loop-tot).  Requires `N ≥ 1` (`[NeZero N]`):
the slice angle is `θ/N`, and `N = 0` has no intended product-formula
reading.  The Trotter error `W(θ/N)^N − e^{-iθH}` is **not** part of this
statement. -/
theorem tfimDeriv :
    DerivTot (Ppre n ψ hψ) (tfimProg n N θ ca cb) (Qpost n N θ ca cb ψ hψ) :=
  DerivTot.conseq (pre_le n N θ ca cb ψ hψ)
    (DerivTot.seq (DerivTot.assign (fun σ => (0, σ.2)) (J n N θ ca cb ψ hψ))
      (loopDeriv n N θ ca cb ψ hψ))
    (post_le n N θ ca cb ψ hψ)

/-- **The semantic content**, through soundness (L-4): all the mass of a
register in `∣ψ⟩` terminates, in `∣W(θ/N)^N ψ⟩` — over every input density
operator, by the effect semantics of `validTot`.  Requires `N ≥ 1`
(`[NeZero N]`), as `tfimDeriv` does. -/
theorem tfimValid :
    validTot (Ppre n ψ hψ) (tfimProg n N θ ca cb) (Qpost n N θ ca cb ψ hψ) :=
  (tfimDeriv n N θ ca cb ψ hψ).sound

/-! ## §7b. The closed form: the postcondition as operator exponentials

`Qpost` names the state through the circuit's own layer composite `W(θ/N)^N`.
The closed-form finals below restate it against the **independently defined**
operators of the model: the Hamiltonians `HX = Σ_j (a j)·X_j`,
`HZZ = Σ_j (b j)·Z_jZ_{j+1}` and the operator exponential `expOp`
(`Qhl/HSpace/OperatorExp.lean`) — the postcondition is literally the
first-order product formula `(e^{-i(θ/N)·HZZ} e^{-i(θ/N)·HX})^N ∣ψ⟩`.  The
bridge is the pair of operator equalities `AOp_eq_expOp`/`BOp_eq_expOp`
(`Qhl/Register/TFIM.lean` §5); the derivation is `tfimDeriv` closed by one
more (R-Conseq). -/

omit [NeZero n] hN in
/-- The product-formula operator power equals the layer-composite iterate:
`(e^{-i(θ/N)·HZZ} ∘ e^{-i(θ/N)·HX})^N ∣ψ⟩ = W(θ/N)^N ∣ψ⟩`, by the two
operator equalities and `wIter_eq_pow`. -/
theorem stepPow_eq :
    ((expOp ((-(Complex.I * ((θ / (N : ℝ)) : ℂ))) • HZZ n cb) ∘ₗ
        expOp ((-(Complex.I * ((θ / (N : ℝ)) : ℂ))) • HX n ca)) ^ N) ψ
      = wIter n ca cb (θ / (N : ℝ)) ψ N := by
  rw [show ((θ : ℂ) / ((N : ℝ) : ℂ)) = (((θ / (N : ℝ)) : ℝ) : ℂ) by norm_cast,
    wIter_eq_pow n ca cb (θ / (N : ℝ)) ψ N, ← BOp_eq_expOp, ← AOp_eq_expOp]
  rfl

omit [NeZero n] hN in
include hψ in
theorem norm_stepPow :
    ‖((expOp ((-(Complex.I * ((θ / (N : ℝ)) : ℂ))) • HZZ n cb) ∘ₗ
        expOp ((-(Complex.I * ((θ / (N : ℝ)) : ℂ))) • HX n ca)) ^ N) ψ‖ = 1 := by
  rw [stepPow_eq]
  exact norm_wIter n ca cb _ hψ N

include hψ in
/-- The closed-form postcondition: "the register is in
`(e^{-i(θ/N)·HZZ} e^{-i(θ/N)·HX})^N ∣ψ⟩`" — the product-formula state, stated
with the operator exponentials of the two Hamiltonians. -/
noncomputable def QpostExp : Assn (ℕ × ℕ) (QubitD n) :=
  Assn.ofState
    (((expOp ((-(Complex.I * ((θ / (N : ℝ)) : ℂ))) • HZZ n cb) ∘ₗ
        expOp ((-(Complex.I * ((θ / (N : ℝ)) : ℂ))) • HX n ca)) ^ N) ψ)
    (norm_stepPow n N θ ca cb ψ hψ)

omit [NeZero n] hN in
include hψ in
/-- The circuit postcondition entails the closed-form postcondition: the two
name the same rank-one projector, by `stepPow_eq`. -/
theorem post_le_exp : Qpost n N θ ca cb ψ hψ ≤ QpostExp n N θ ca cb ψ hψ := by
  intro σ
  refine le_of_eq ?_
  rw [Qpost, QpostExp, Assn.ofState_op, Assn.ofState_op, stepPow_eq]

set_option linter.unusedSectionVars false in
include hN in
/-- **The closed-form transverse-field Ising product-formula triple**
`{ ∣ψ⟩⟨ψ∣ } tfimProg { ∣(e^{-i(θ/N)·HZZ} e^{-i(θ/N)·HX})^N ψ⟩⟨…∣ }` is
derivable in `QHL⁺_tot`: the postcondition is the first-order Trotter product
formula itself, stated against the independently defined Hamiltonians `HX`,
`HZZ` and the operator exponential — obtained from `tfimDeriv` by (R-Conseq)
along the operator equalities `AOp_eq_expOp`/`BOp_eq_expOp`.  Requires
`N ≥ 1` (`[NeZero N]`), as `tfimDeriv` does.  The Trotter error
`(e^{-i(θ/N)H_ZZ}e^{-i(θ/N)H_X})^N − e^{-iθH}` is **not** part of this
statement. -/
theorem tfimDerivExp :
    DerivTot (Ppre n ψ hψ) (tfimProg n N θ ca cb) (QpostExp n N θ ca cb ψ hψ) :=
  DerivTot.conseq (Assn.le_refl' _) (tfimDeriv n N θ ca cb ψ hψ)
    (post_le_exp n N θ ca cb ψ hψ)

/-- **The semantic content of the closed form**, through soundness (L-4): all
the mass of a register in `∣ψ⟩` terminates, in the product-formula state
`(e^{-i(θ/N)·HZZ} e^{-i(θ/N)·HX})^N ∣ψ⟩` — over every input density operator.
Requires `N ≥ 1` (`[NeZero N]`). -/
theorem tfimValidExp :
    validTot (Ppre n ψ hψ) (tfimProg n N θ ca cb) (QpostExp n N θ ca cb ψ hψ) :=
  (tfimDerivExp n N θ ca cb ψ hψ).sound

/-! ## §8. Approximation of the target Hamiltonian evolution

The error parameter is fixed by the specification. The program and its
counter updates are unchanged. Scaling the existing derivation and applying
(Rule-Conseq) gives an effect-valued error guarantee for all density operators.
-/

/-- The normalized intended-input predicate for an error tolerance. -/
noncomputable def PpreApprox (ε : ℝ) (hε : 0 ≤ ε) : Assn (ℕ × ℕ) (QubitD n) :=
  (Ppre n ψ hψ).scaled (1 + ε)⁻¹ (approxCoeff_nonneg hε) (approxCoeff_le_one hε)

/-- The target-evolution predicate with the normalized identity error. -/
noncomputable def QpostApprox (ε : ℝ) (hε : 0 ≤ ε) : Assn (ℕ × ℕ) (QubitD n) :=
  (Assn.ofState (evolution n ca cb θ ψ) (by rw [norm_evolution]; exact hψ)).approx ε hε

/-- An operator-norm error bound transfers the exact circuit derivation to
an approximate specification against the full Hamiltonian evolution. -/
theorem tfimDerivApprox_of_norm (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ‖((WOp n ca cb (θ / (N : ℝ))) ^ N).toContinuousLinearMap -
      (evolution n ca cb θ).toContinuousLinearMap‖ ≤ ε) :
    DerivTot (PpreApprox n ψ hψ ε hε) (tfimProg n N θ ca cb)
      (QpostApprox n θ ca cb ψ hψ ε hε) := by
  exact (tfimDeriv n N θ ca cb ψ hψ).approx_state
    (v := evolution n ca cb θ ψ) (hv := by rw [norm_evolution]; exact hψ) ε hε
    (norm_wIter_sub_evolution_of_norm_le n ca cb N θ ψ hψ ε herr)

/-- The approximate Trotter triple, with the proved first-order error bound.
The tolerance is a specification parameter; it is not a premise asserting
that the circuit is already close to the target. -/
theorem tfimDerivApprox (ε : ℝ)
    (herr : trotterErrorBound n ca cb N θ ≤ ε) :
    DerivTot
      (PpreApprox n ψ hψ ε ((trotterErrorBound_nonneg n ca cb N θ).trans herr))
      (tfimProg n N θ ca cb)
      (QpostApprox n θ ca cb ψ hψ ε ((trotterErrorBound_nonneg n ca cb N θ).trans herr)) :=
  tfimDerivApprox_of_norm n N θ ca cb ψ hψ ε
    ((trotterErrorBound_nonneg n ca cb N θ).trans herr)
    ((norm_product_sub_evolution_le n ca cb N θ).trans herr)

/-- Approximate correctness for every input density operator, through soundness. -/
theorem tfimValidApprox (ε : ℝ)
    (herr : trotterErrorBound n ca cb N θ ≤ ε) :
    validTot
      (PpreApprox n ψ hψ ε ((trotterErrorBound_nonneg n ca cb N θ).trans herr))
      (tfimProg n N θ ca cb)
      (QpostApprox n θ ca cb ψ hψ ε ((trotterErrorBound_nonneg n ca cb N θ).trans herr)) :=
  (tfimDerivApprox n N θ ca cb ψ hψ ε herr).sound

/-- A coefficient-only sufficient condition for the approximate Trotter triple. -/
theorem tfimDerivApprox_of_coefficients (ε : ℝ) (hε : 0 ≤ ε)
    (herr : θ ^ 2 / (N : ℝ) *
      ∑ j : Fin (n - 1), |cb j| * (|ca (loCell n j)| + |ca (hiCell n j)|) ≤ ε) :
    DerivTot (PpreApprox n ψ hψ ε hε) (tfimProg n N θ ca cb)
      (QpostApprox n θ ca cb ψ hψ ε hε) :=
  tfimDerivApprox n N θ ca cb ψ hψ ε
    ((trotterErrorBound_le_coefficients n ca cb N θ).trans herr)

/-- The coefficient-based guarantee for all input density operators. -/
theorem tfimValidApprox_of_coefficients (ε : ℝ) (hε : 0 ≤ ε)
    (herr : θ ^ 2 / (N : ℝ) *
      ∑ j : Fin (n - 1), |cb j| * (|ca (loCell n j)| + |ca (hiCell n j)|) ≤ ε) :
    validTot (PpreApprox n ψ hψ ε hε) (tfimProg n N θ ca cb)
      (QpostApprox n θ ca cb ψ hψ ε hε) :=
  (tfimDerivApprox_of_coefficients n N θ ca cb ψ hψ ε hε herr).sound

/-! ## §9. Non-vacuity -/


/-- A concrete input the precondition accepts with all of its mass: the pure
state `∣ψ⟩⟨ψ∣` at the zero store. -/
noncomputable def inputState : CQState (ℕ × ℕ) (QubitD n) :=
  ⟨(0, 0), ⟨outerLM ψ ψ, isPositive_outerLM_self ψ⟩⟩

omit [NeZero n] in
include hψ in
/-- **The precondition is satisfiable**: it has expectation `1` — the full
mass — in the concrete input state, so the triple is not vacuous. -/
theorem tfimPre_expect_one :
    expectE (Ppre n ψ hψ).op (inputState n ψ) = 1 := by
  have hin : (⟪ψ, ψ⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  rw [expectE, expect,
    show (inputState n ψ).q.op = outerLM ψ ψ from rfl,
    show (Ppre n ψ hψ).op (inputState n ψ).cls = outerLM ψ ψ from rfl,
    trace_outerLM_comp, outerLM_apply, inner_smul_right, hin]
  simp

/-- The approximate precondition has strictly positive expectation on its intended input. -/
theorem tfimApproxPre_expect (ε : ℝ) (hε : 0 ≤ ε) :
    expectE (PpreApprox n ψ hψ ε hε).op (inputState n ψ) =
      ENNReal.ofReal ((1 + ε)⁻¹) := by
  have hin : (⟪ψ, ψ⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  simp only [expectE, expect, PpreApprox, Assn.scaled_op, Ppre, Assn.ofState_op,
    inputState, trace_outerLM_comp, LinearMap.smul_apply, outerLM_apply,
    inner_smul_right, hin, mul_one, Complex.ofReal_re]

end

end Qhl.TrotterTFIM

#print axioms Qhl.TrotterTFIM.tfimDeriv
#print axioms Qhl.TrotterTFIM.tfimValid
#print axioms Qhl.TrotterTFIM.tfimDerivExp
#print axioms Qhl.TrotterTFIM.tfimValidExp
#print axioms Qhl.TrotterTFIM.tfimPre_expect_one
#print axioms Qhl.AOp_pmState
#print axioms Qhl.BOp_deltav
#print axioms Qhl.AOp_eq_expOp
#print axioms Qhl.BOp_eq_expOp
#print axioms Qhl.expOp_eigenvector

#print axioms Qhl.TrotterTFIM.tfimDerivApprox
#print axioms Qhl.TrotterTFIM.tfimValidApprox
#print axioms Qhl.TrotterTFIM.tfimApproxPre_expect

#print axioms Qhl.TrotterTFIM.tfimDerivApprox_of_coefficients
#print axioms Qhl.TrotterTFIM.tfimValidApprox_of_coefficients

/-! # Literal-parameter TFIM through source derivations -/
namespace Qhl.TrotterTFIMSource
open Qhl Finset TrotterTFIM
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal
variable (n N : ℕ) [NeZero n] (θ : ℝ) (ca : Fin n → ℝ) (cb : Fin (n - 1) → ℝ)
variable (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1)
noncomputable def state (k : ℕ) (_σ : ℕ × ℕ) := sW n N θ ca cb ψ k
noncomputable def xState (k : ℕ) (σ : ℕ × ℕ) := chi1 n N θ ca cb ψ σ.1 k
noncomputable def zzState (k : ℕ) (σ : ℕ × ℕ) := chi2 n N θ ca cb ψ σ.1 k
include hψ in
theorem norm_state (k : ℕ) (σ : ℕ × ℕ) : ‖state n N θ ca cb ψ k σ‖ = 1 :=
  norm_sW n N θ ca cb ψ hψ k
include hψ in
theorem norm_xState (k : ℕ) (σ : ℕ × ℕ) : ‖xState n N θ ca cb ψ k σ‖ = 1 :=
  norm_chi1 n N θ ca cb ψ hψ σ.1 k
include hψ in
theorem norm_zzState (k : ℕ) (σ : ℕ × ℕ) : ‖zzState n N θ ca cb ψ k σ‖ = 1 :=
  norm_chi2 n N θ ca cb ψ hψ σ.1 k
theorem sliceIdentitySource (φ : ℕ → Prop) :
    SourceDerivTot (SourceAssertion.identity (D := QubitD n) (fun σ => φ σ.1))
      (slice n N θ ca cb) (SourceAssertion.identity (D := QubitD n) (fun σ => φ σ.1)) := by
  apply SourceDerivTot.seq (B := SourceAssertion.identity (D := QubitD n) (fun σ => φ σ.1))
  · exact SourceDerivTot.countedIdentity (CounterLens.snd ℕ) (fun _ => n) (fun σ => φ σ.1)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) _
      (SourceDerivTot.unitary_identity _ _ _ (fun _ _ _ _ _ => Subsingleton.elim _ _))
      (fun _ => SourceDerivTot.unitary_identity _ _ _ (fun _ _ _ _ _ => Subsingleton.elim _ _))
  · apply SourceDerivTot.countedIdentity (CounterLens.snd ℕ) (fun _ => n - 1) (fun σ => φ σ.1)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) _
    · exact SourceDerivTot.unitary_identity _ _ _ (fun σ hσ =>
        (Reg.pair _ _ (zzCells_ne n hσ.2)).inj)
    · intro k
      exact SourceDerivTot.unitary_identity _ _ _ (fun σ hσ => (Reg.pair _ _ (zzCells_ne n
        hσ.2.1)).inj)

theorem xChainScaledSource (φ : ℕ → Prop)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    SourceDerivTot (SourceAssertion.ofAssn ((Jfam n N θ ca cb ψ hψ).scaledBy (fun _ => a)
        (fun _ => ha0) (fun _ => ha1)) (fun σ => φ σ.1))
      (xLayer n N θ ca) (SourceAssertion.ofAssn
        ((Amid n N θ ca cb ψ hψ).scaledBy (fun _ => a)
          (fun _ => ha0) (fun _ => ha1)) (fun σ => φ σ.1)) :=
  SourceDerivTot.countedStateChain_scaled (CounterLens.snd ℕ) (fun _ => n) (fun σ => φ σ.1)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun _ => a) (fun _ => ha0) (fun _ => ha1) (fun _ _ => rfl)
    (xState n N θ ca cb ψ) (norm_xState n N θ ca cb ψ hψ) (fun _ _ _ => rfl)
    (fun σ _ => chi1_zero n N θ ca cb ψ σ.1)
    (fun σ _ => chi1_top n N θ ca cb ψ σ.1)
    (SourceDerivTot.countedRung_fam_scaled (TrotterTFIM.xReg n) (xGateE n N θ ca)
      (fun _ => a) (fun _ => ha0) (fun _ => ha1)
      (fun σ => norm_xState n N θ ca cb ψ hψ σ.2 σ)
      (fun σ => norm_xState n N θ ca cb ψ hψ (σ.2 + 1) σ)
      (fun σ hσ => by
        have hk : σ.2 < n := hσ.2
        refine ⟨fun a b _ => Subsingleton.elim a b, ?_⟩
        change Qhl.xGate n ca (θ / (N : ℝ)) (cell n σ.2)
            (chi1 n N θ ca cb ψ σ.1 σ.2) = _
        rw [show cell n σ.2 = ⟨σ.2, hk⟩ from cell_eq_mk n hk]
        exact chi1_succ n N θ ca cb ψ σ.1 ⟨σ.2, hk⟩))
    (fun _ => SourceDerivTot.unitary_identity _ _ _
      (fun _ _ _ _ _ => Subsingleton.elim _ _))

theorem zzChainScaledSource (φ : ℕ → Prop)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    SourceDerivTot (SourceAssertion.ofAssn ((Amid n N θ ca cb ψ hψ).scaledBy (fun _ => a)
        (fun _ => ha0) (fun _ => ha1)) (fun σ => φ σ.1))
      (zzLayer n N θ cb) (SourceAssertion.ofAssn ((Astep n N θ ca cb ψ hψ).scaledBy (fun _ => a)
        (fun _ => ha0) (fun _ => ha1)) (fun σ => φ σ.1)) :=
  SourceDerivTot.countedStateChain_scaled (CounterLens.snd ℕ) (fun _ => n - 1) (fun σ => φ σ.1)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun _ => a) (fun _ => ha0) (fun _ => ha1) (fun _ _ => rfl)
    (zzState n N θ ca cb ψ) (norm_zzState n N θ ca cb ψ hψ) (fun _ _ _ => rfl)
    (fun _ _ => rfl)
    (fun σ _ => chi2_top n N θ ca cb ψ σ.1)
    (SourceDerivTot.countedRung_fam_scaled (TrotterTFIM.zzReg n) (zzGateE n N θ cb)
      (fun _ => a) (fun _ => ha0) (fun _ => ha1)
      (fun σ => norm_zzState n N θ ca cb ψ hψ σ.2 σ)
      (fun σ => norm_zzState n N θ ca cb ψ hψ (σ.2 + 1) σ)
      (fun σ hσ => by
        have hk : σ.2 < n - 1 := hσ.2
        have hne := zzCells_ne n hk
        refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
        change regLift (Reg.pair (cell n σ.2) (cell n (σ.2 + 1)) hne)
            (TrotterTFIM.zzGateE n N θ cb σ)
            (chi2 n N θ ca cb ψ σ.1 σ.2) = _
        rw [show TrotterTFIM.zzGateE n N θ cb σ =
            pairGate (D := QubitD n) (cell n σ.2) (cell n (σ.2 + 1)) hne
              (Rzz (2 * cb ⟨σ.2, hk⟩ * (θ / (N : ℝ)))) from by
                simp only [TrotterTFIM.zzGateE, dif_pos hk],
          zzLift_eq n cb (θ / (N : ℝ)) ⟨σ.2, hk⟩ hne
            (Fin.ext (cell_val n (by omega))) (Fin.ext (cell_val n (by omega)))]
        exact chi2_succ n N θ ca cb ψ σ.1 ⟨σ.2, hk⟩))
    (fun _ => SourceDerivTot.unitary_identity _ _ _ (fun σ hσ =>
      (Reg.pair _ _ (zzCells_ne n hσ.2.1)).inj))

theorem scaledSourceDeriv (φ : Prop)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    SourceDerivTot (SourceAssertion.ofAssn ((Ppre n ψ hψ).scaledBy (fun _ => a)
        (fun _ => ha0) (fun _ => ha1)) (fun _ => φ)) (tfimProg n N θ ca cb)
      (SourceAssertion.ofAssn ((Qpost n N θ ca cb ψ hψ).scaledBy (fun _ => a) (fun _ => ha0)
        (fun _ => ha1)) (fun _ => φ)) :=
  SourceDerivTot.countedStateChain_scaled (CounterLens.fst ℕ) (fun _ => N) (fun _ => φ)
    (hv₀ := fun _ => hψ) (hv₁ := norm_state n N θ ca cb ψ hψ N)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun _ => a) (fun _ => ha0) (fun _ => ha1) (fun _ _ => rfl)
    (state n N θ ca cb ψ) (norm_state n N θ ca cb ψ hψ) (fun _ _ _ => rfl)
    (fun _ _ => sW_zero n N θ ca cb ψ)
    (fun _ _ => rfl)
    ((xChainScaledSource n N θ ca cb ψ hψ (fun i => φ ∧ i < N) a ha0 ha1).seq
      (zzChainScaledSource n N θ ca cb ψ hψ (fun i => φ ∧ i < N) a ha0 ha1))
    (fun z => sliceIdentitySource n N θ ca cb (fun i => φ ∧ i < N ∧ (↑(N - i) : Int) = z))



variable [hN : NeZero N]

set_option linter.unusedSectionVars false in
include hN in
/-- The exact original TFIM program and pure-state endpoints through source rules. -/
theorem tfimSourceDeriv :
    SourceDerivTot (SourceAssertion.ofAssn (Ppre n ψ hψ) (fun _ => True))
      (tfimProg n N θ ca cb)
      (SourceAssertion.ofAssn (Qpost n N θ ca cb ψ hψ) (fun _ => True)) := by
  have h := scaledSourceDeriv n N θ ca cb ψ hψ True 1 (by norm_num) (by norm_num)
  have hs (A : Assn (ℕ × ℕ) (QubitD n)) :
      A.scaledBy (fun _ => 1) (fun _ => by norm_num) (fun _ => by norm_num) = A := by
    ext σ
    simp [Assn.scaledBy_op]
  simpa only [hs] using h

/-- Original exact semantic target, from source soundness. -/
theorem tfimSourceValid : validTot (Ppre n ψ hψ) (tfimProg n N θ ca cb)
    (Qpost n N θ ca cb ψ hψ) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using (tfimSourceDeriv n N θ ca cb ψ hψ).sound

/-- The equivalent exponential endpoint follows by source consequence. -/
theorem tfimSourceDerivExp :
    SourceDerivTot (SourceAssertion.ofAssn (Ppre n ψ hψ) (fun _ => True))
      (tfimProg n N θ ca cb)
      (SourceAssertion.ofAssn (QpostExp n N θ ca cb ψ hψ) (fun _ => True)) :=
  .conseq (SourceAssertion.entails_refl _) (tfimSourceDeriv n N θ ca cb ψ hψ)
    (SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h)
      (fun σ _ => post_le_exp n N θ ca cb ψ hψ σ))

set_option linter.unusedSectionVars false in
include hN in
/-- A norm error estimate gives the original normalized approximate cq endpoints. -/
theorem tfimSourceDerivApprox_of_norm (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ‖((WOp n ca cb (θ / (N : ℝ))) ^ N).toContinuousLinearMap -
      (evolution n ca cb θ).toContinuousLinearMap‖ ≤ ε) :
    SourceDerivTot (SourceAssertion.ofAssn (PpreApprox n ψ hψ ε hε) (fun _ => True))
      (tfimProg n N θ ca cb)
      (SourceAssertion.ofAssn (QpostApprox n θ ca cb ψ hψ ε hε) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (scaledSourceDeriv n N θ ca cb ψ hψ True (1 + ε)⁻¹
      (approxCoeff_nonneg hε) (approxCoeff_le_one hε)) ?_
  apply SourceAssertion.entails_ofAssn
  · intro _ h; exact h
  · intro σ _
    rw [Assn.scaledBy_op, QpostApprox, Assn.approx_op_eq]
    apply real_smul_operator_mono _ (approxCoeff_nonneg hε)
    exact outerLM_self_le_add_of_norm_sub_le _ _ (norm_wIter n ca cb _ hψ N)
      (by rw [norm_evolution]; exact hψ) hε
      (norm_wIter_sub_evolution_of_norm_le n ca cb N θ ψ hψ ε herr)

/-- Exponential semantic endpoint through source soundness. -/
theorem tfimSourceValidExp : validTot (Ppre n ψ hψ) (tfimProg n N θ ca cb)
    (QpostExp n N θ ca cb ψ hψ) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using
    (tfimSourceDerivExp n N θ ca cb ψ hψ).sound

/-- The norm-bound semantic specification, through source soundness. -/
theorem tfimSourceValidApprox_of_norm (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ‖((WOp n ca cb (θ / (N : ℝ))) ^ N).toContinuousLinearMap -
      (evolution n ca cb θ).toContinuousLinearMap‖ ≤ ε) :
    validTot (PpreApprox n ψ hψ ε hε) (tfimProg n N θ ca cb)
      (QpostApprox n θ ca cb ψ hψ ε hε) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using
    (tfimSourceDerivApprox_of_norm n N θ ca cb ψ hψ ε hε herr).sound

/-- Source approximate correctness with the proved Trotter error bound. -/
theorem tfimSourceDerivApprox (ε : ℝ) (herr : trotterErrorBound n ca cb N θ ≤ ε) :
    SourceDerivTot
      (SourceAssertion.ofAssn
        (PpreApprox n ψ hψ ε ((trotterErrorBound_nonneg n ca cb N θ).trans herr))
        (fun _ => True)) (tfimProg n N θ ca cb)
      (SourceAssertion.ofAssn
        (QpostApprox n θ ca cb ψ hψ ε ((trotterErrorBound_nonneg n ca cb N θ).trans herr))
        (fun _ => True)) :=
  tfimSourceDerivApprox_of_norm n N θ ca cb ψ hψ ε
    ((trotterErrorBound_nonneg n ca cb N θ).trans herr)
    ((norm_product_sub_evolution_le n ca cb N θ).trans herr)

/-- Exact original approximate semantic target, from source soundness. -/
theorem tfimSourceValidApprox (ε : ℝ) (herr : trotterErrorBound n ca cb N θ ≤ ε) :
    validTot
      (PpreApprox n ψ hψ ε ((trotterErrorBound_nonneg n ca cb N θ).trans herr))
      (tfimProg n N θ ca cb)
      (QpostApprox n θ ca cb ψ hψ ε ((trotterErrorBound_nonneg n ca cb N θ).trans herr)) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using
    (tfimSourceDerivApprox n N θ ca cb ψ hψ ε herr).sound

/-- Coefficient-only sufficient error bound, preserving the original endpoints. -/
theorem tfimSourceDerivApprox_of_coefficients (ε : ℝ) (hε : 0 ≤ ε)
    (herr : θ ^ 2 / (N : ℝ) *
      ∑ j : Fin (n - 1), |cb j| * (|ca (loCell n j)| + |ca (hiCell n j)|) ≤ ε) :
    SourceDerivTot
      (SourceAssertion.ofAssn (PpreApprox n ψ hψ ε hε) (fun _ => True))
      (tfimProg n N θ ca cb)
      (SourceAssertion.ofAssn (QpostApprox n θ ca cb ψ hψ ε hε) (fun _ => True)) :=
  tfimSourceDerivApprox n N θ ca cb ψ hψ ε
    ((trotterErrorBound_le_coefficients n ca cb N θ).trans herr)

/-- Coefficient-error semantic guarantee through source soundness. -/
theorem tfimSourceValidApprox_of_coefficients (ε : ℝ) (hε : 0 ≤ ε)
    (herr : θ ^ 2 / (N : ℝ) *
      ∑ j : Fin (n - 1), |cb j| * (|ca (loCell n j)| + |ca (hiCell n j)|) ≤ ε) :
    validTot (PpreApprox n ψ hψ ε hε) (tfimProg n N θ ca cb)
      (QpostApprox n θ ca cb ψ hψ ε hε) := by
  simpa only [SourceAssertion.toAssn_ofAssn_true] using
    (tfimSourceDerivApprox_of_coefficients n N θ ca cb ψ hψ ε hε herr).sound

end Qhl.TrotterTFIMSource

#print axioms Qhl.TrotterTFIMSource.tfimSourceDeriv
#print axioms Qhl.TrotterTFIMSource.tfimSourceDerivExp
#print axioms Qhl.TrotterTFIMSource.tfimSourceDerivApprox
#print axioms Qhl.TrotterTFIMSource.tfimSourceValidApprox

#print axioms Qhl.TrotterTFIMSource.tfimSourceValid
#print axioms Qhl.TrotterTFIMSource.tfimSourceValidExp
#print axioms Qhl.TrotterTFIMSource.tfimSourceDerivApprox_of_norm
#print axioms Qhl.TrotterTFIMSource.tfimSourceValidApprox_of_norm
#print axioms Qhl.TrotterTFIMSource.tfimSourceDerivApprox_of_coefficients
#print axioms Qhl.TrotterTFIMSource.tfimSourceValidApprox_of_coefficients
