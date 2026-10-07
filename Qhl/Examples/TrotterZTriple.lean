import Qhl.Logic.Soundness
import Qhl.Gate.Qubit
import Qhl.HSpace.LocalGate
import Qhl.Register.Qubits

/-!
# Trotterized simulation of `H = Z` on one qubit, as a total-correctness triple

The Hamiltonian-simulation task `Rz(θ) = e^{-i(θ/2)Z}` on a single qubit
(the half-angle convention of `Qhl/Gate/Qubit.lean`), built by the
first-order Trotter product formula: split the evolution into `N` equal slices
and apply the small `z`-rotation `Rz(θ/N)` once per slice,

```
i := 0;  while i < N do  q *= Rz(θ/N);  i := i + 1  od
```

over the classical state space `σT = ℕ` (the step counter) on a single-qubit
world. Because the Hamiltonian has a single term, `Z`, every slice commutes with
every other, so the product formula is **exact**: `N` steps of `Rz(θ/N)`
compose to `Rz(θ)` with no Trotter-error term. The correctness therefore stays
entirely inside the printed proof system `QHL⁺_tot` — no meta-level /
almost-sure reasoning, no error analysis. The loop is a genuine ranked `while`
closed by **(R-Loop-tot)** — `DerivTot.whileLoop` — with ranking function
`t i = N − i`.

For an arbitrary single-qubit unit ket `ψ` the triple is

```
{ ∣ψ⟩⟨ψ∣ }  i := 0; while i < N do q *= Rz(θ/N); i := i+1 od  { ∣Rz(θ)ψ⟩⟨Rz(θ)ψ∣ }.
```

The loop invariant is "after `i` steps the qubit is in `Rz((θ·i)/N)∣ψ⟩`",
rendered as the interpolating product state `stateAt i` and saturated at `N`
(via `min i N`, exactly as `plusAt` saturates in `ParallelHadamardTriple`) so
that the post-guard classical states `i ≥ N` all read the final state `Rz(θ)∣ψ⟩`.
The single piece of state algebra is `Rz_Rz_apply` — one more `Rz(θ/N)` advances
the accumulated rotation by one slice — a program-agnostic gate law banked in
`Qhl/Gate/Qubit.lean`. Everything else is the proof system: two axioms (Ax-Uni,
Ax-Ass), (R-Seq), (R-Conseq) and the loop rule.
-/

namespace Qhl.TrotterZ

open Qhl Finset
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal

section

variable (N : ℕ) [NeZero N] (θ : ℝ) (ψ : 𝕢) (hψ : ‖ψ‖ = 1)

/-! ## §1. The fixture: one qubit cell, the counter as classical state -/

/-- The single qubit the program acts on: the one cell of a one-qubit world. -/
def cell : QubitL 1 := 0

/-- The register expression `q` of the loop body: the constant one-cell
register naming the only qubit. -/
def regE : RegExpr ℕ (QubitL 1) 1 := fun _ => (Reg.single cell).toFun

/-- The paper's `Dist(q̄)` (eq (2)) is free for a one-cell register. -/
theorem distE (σ : ℕ) : Function.Injective (regE σ) := (Reg.single cell).inj

/-- The Trotter-step gate `Rz(θ/N)` on the tuple space of the one-cell
register. -/
noncomputable def gate (σ : ℕ) : UnitaryOp (TSpace (QubitD 1) (regE σ)) :=
  singleGate (QubitD 1) cell (Rz (θ / (N : ℝ)))

/-- `Rz(θ/N)` on the qubit, extended to the whole world: the library one-site
gate `gateAt`. -/
noncomputable def K : EndM (QubitD 1) (univ : Finset (QubitL 1)) :=
  gateAt (QubitL 1) cell (Rz (θ / (N : ℝ)))

theorem regLift_regE (σ : ℕ) : regLift ⟨regE σ, distE σ⟩ (gate N θ σ) = K N θ := rfl

theorem isUnitary_K : IsUnitary (K N θ) := isUnitary_gateAt (QubitL 1) cell (Rz (θ / (N : ℝ)))

/-- The loop guard `i < N`. -/
def bGuard (σ : ℕ) : Bool := decide (σ < N)

/-- The loop body `q *= Rz(θ/N); i := i + 1`. -/
noncomputable def body : Prog ℕ (QubitD 1) :=
  (Prog.unitary 1 regE (gate N θ)).seq (Prog.assign fun σ => σ + 1)

/-- The program `i := 0; while i < N do q *= Rz(θ/N); i := i + 1 od`. -/
noncomputable def trotterProg : Prog ℕ (QubitD 1) :=
  (Prog.assign fun _ => 0).seq (Prog.while (bGuard N) (body N θ))

/-! ## §2. The interpolating (saturating) accumulated-rotation state -/

/-- The accumulated rotation angle after `σ` steps, capped at the final angle
`θ`: `θ·(min σ N)/N`. Capping at `N` (as `plusAt` saturates in the parallel
Hadamard example) makes the state stationary once the loop has finished. -/
noncomputable def capAng (σ : ℕ) : ℝ := θ * ((min σ N : ℕ) : ℝ) / (N : ℝ)

/-- The single factor of the interpolating state: `Rz((θ·min σ N)/N)∣ψ⟩`. -/
noncomputable def stepVec (σ : ℕ) (_ : QubitL 1) : 𝕢 := (Rz (capAng N θ σ) : 𝕢 →ₗ[ℂ] 𝕢) ψ

/-- The interpolating state after `σ` steps: the qubit in `Rz((θ·min σ N)/N)∣ψ⟩`,
as the library product state `prodV` (of a single factor). -/
noncomputable def stateAt (σ : ℕ) : HS (QubitD 1) (univ : Finset (QubitL 1)) :=
  prodV (QubitD 1) (stepVec N θ ψ σ)

include hψ in
theorem norm_stateAt (σ : ℕ) : ‖stateAt N θ ψ σ‖ = 1 := by
  refine norm_prodV_eq_one (D := QubitD 1) (W := (univ : Finset (QubitL 1)))
    (stepVec N θ ψ σ) ?_
  intro i
  simp only [stepVec]
  exact norm_unitaryOp_apply (Rz (capAng N θ σ)) hψ

omit [NeZero N] in
/-- At `σ = 0` the accumulated rotation is `Rz 0 = 1`, so the state is `∣ψ⟩`. -/
theorem stateAt_zero : stateAt N θ ψ 0 = prodV (QubitD 1) (fun _ => ψ) := by
  refine prodV_congr (QubitD 1) fun j _ => ?_
  simp only [stepVec, show capAng N θ 0 = 0 by simp [capAng], Rz_zero_apply]

/-- At `σ = N` the accumulated rotation is the full `Rz θ`, so the state is
`∣Rz(θ)ψ⟩`. -/
theorem stateAt_top : stateAt N θ ψ N = prodV (QubitD 1) (fun _ => (Rz θ : 𝕢 →ₗ[ℂ] 𝕢) ψ) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  refine prodV_congr (QubitD 1) fun j _ => ?_
  simp only [stepVec, show capAng N θ N = θ by rw [capAng, min_self]; field_simp]

/-- Beyond `σ = N` the state does not move: the accumulated rotation is capped
at `θ`. -/
theorem stateAt_of_ge {σ : ℕ} (h : N ≤ σ) : stateAt N θ ψ σ = stateAt N θ ψ N := by
  refine prodV_congr (QubitD 1) fun j _ => ?_
  simp only [stepVec]
  rw [show capAng N θ σ = capAng N θ N by simp only [capAng, min_eq_right h, min_self]]

/-! ## §3. The one real computation: one slice advances the rotation -/

/-- **The computation**: one `Rz(θ/N)` on the qubit advances the interpolating
state one step, `Rz((θ·σ)/N)∣ψ⟩ ↦ Rz((θ·(σ+1))/N)∣ψ⟩`. The library one-site
bridge `gateAt_prodV` places the gate on the single factor; `Rz_Rz_apply` is the
rotation-addition law `Rz(θ/N) ∘ Rz((θ·σ)/N) = Rz((θ·(σ+1))/N)`. -/
theorem K_stateAt {σ : ℕ} (hσ : σ < N) : K N θ (stateAt N θ ψ σ) = stateAt N θ ψ (σ + 1) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hb := gateAt_prodV (QubitL 1) cell (Rz (θ / (N : ℝ))) (stepVec N θ ψ σ)
  refine hb.trans (prodV_congr (QubitD 1) fun j _ => ?_)
  have hj : j = cell := Subsingleton.elim j cell
  subst hj
  rw [Function.update_self]
  simp only [stepVec]
  rw [Rz_Rz_apply, show θ / (N : ℝ) + capAng N θ σ = capAng N θ (σ + 1) by
    have h1 : min σ N = σ := min_eq_left (le_of_lt hσ)
    have h2 : min (σ + 1) N = σ + 1 := min_eq_left (Nat.succ_le_of_lt hσ)
    simp only [capAng, h1, h2]; push_cast; field_simp; ring]

/-! ## §4. The assertions, the loop invariant, and the derivation -/

include hψ in
/-- The loop invariant: "the qubit is in the interpolating state `Rz((θ·i)/N)∣ψ⟩`". -/
noncomputable def J : Assn ℕ (QubitD 1) :=
  ⟨fun σ => outerLM (stateAt N θ ψ σ) (stateAt N θ ψ σ),
    fun σ => isEffect_outerLM_self (norm_stateAt N θ ψ hψ σ)⟩

@[simp] theorem J_op (σ : ℕ) :
    (J N θ ψ hψ).op σ = outerLM (stateAt N θ ψ σ) (stateAt N θ ψ σ) := rfl

include hψ in
/-- The precondition "the qubit is in `∣ψ⟩`". -/
noncomputable def Ppre : Assn ℕ (QubitD 1) :=
  Assn.ofState (prodV (QubitD 1) (fun _ => ψ)) (norm_prodV_eq_one _ (fun _ => hψ))

include hψ in
/-- The postcondition "the qubit is in `∣Rz(θ)ψ⟩`". -/
noncomputable def Qpost : Assn ℕ (QubitD 1) :=
  Assn.ofState (prodV (QubitD 1) (fun _ => (Rz θ : 𝕢 →ₗ[ℂ] 𝕢) ψ))
    (norm_prodV_eq_one _ (fun _ => norm_unitaryOp_apply (Rz θ) hψ))

/-- The ranking function of (R-Loop-tot): the number of slices still to do. -/
def rank (σ : ℕ) : ℕ := N - σ

/-- The body's premise for the ranking value `m`: (Ax-Uni) and (Ax-Ass), glued
by (R-Seq), with (R-Conseq) discharging the invariant step — the entailment it
needs is exactly `K_stateAt`. -/
theorem premise_le (m : ℕ) :
    ((J N θ ψ hψ).mand (bGuard N)).mask (fun σ => rank N σ = m)
      ≤ (((J N θ ψ hψ).mask fun σ => rank N σ < m).comp fun σ => σ + 1).unitaryPre
          regE (gate N θ) := by
  intro σ
  by_cases hm : rank N σ = m
  · by_cases hg : bGuard N σ = true
    · have hσ : σ < N := by simpa [bGuard] using hg
      have hlt : rank N (σ + 1) < m := by simp only [rank] at hm ⊢; omega
      refine le_of_eq ?_
      rw [Assn.mask_op_of_pos (A := (J N θ ψ hψ).mand (bGuard N))
          (φ := fun σ => rank N σ = m) (σ := σ) hm,
        Assn.mand_op_of_true (A := J N θ ψ hψ) (b := bGuard N) (σ := σ) hg,
        Assn.unitaryPre_op_of_dist _ regE (gate N θ) (distE σ), regLift_regE,
        Assn.comp_op, Assn.mask_op_of_pos (A := J N θ ψ hψ)
          (φ := fun σ => rank N σ < m) (σ := σ + 1) hlt, J_op, J_op,
        adjoint_comp_outerLM_comp, ← K_stateAt N θ ψ hσ,
        adjoint_apply_apply (isUnitary_K N θ)]
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := (J N θ ψ hψ).mand (bGuard N))
        (φ := fun σ => rank N σ = m) (σ := σ) hm]
      exact Assn.mand_op_of_false (A := J N θ ψ hψ) (b := bGuard N) (σ := σ) (by simpa using hg)
  · exact Assn.op_zero_le (Assn.mask_op_of_neg (A := (J N θ ψ hψ).mand (bGuard N))
      (φ := fun σ => rank N σ = m) (σ := σ) hm)

theorem bodyDeriv (m : ℕ) :
    DerivTot (((J N θ ψ hψ).mand (bGuard N)).mask fun σ => rank N σ = m) (body N θ)
      ((J N θ ψ hψ).mask fun σ => rank N σ < m) :=
  DerivTot.seq
    (DerivTot.conseq (premise_le N θ ψ hψ m)
      (DerivTot.unitary regE (gate N θ) _) (Assn.le_refl' _))
    (DerivTot.assign (fun σ => σ + 1) ((J N θ ψ hψ).mask fun σ => rank N σ < m))

/-- **(R-Loop-tot)**: the invariant `J` with ranking function `rank`. -/
theorem loopDeriv :
    DerivTot (J N θ ψ hψ) (Prog.while (bGuard N) (body N θ)) ((J N θ ψ hψ).mandNot (bGuard N)) :=
  DerivTot.whileLoop (rank N) (bodyDeriv N θ ψ hψ)

theorem pre_le : Ppre ψ hψ ≤ (J N θ ψ hψ).comp fun _ => 0 := by
  intro σ
  refine le_of_eq ?_
  rw [Ppre, Assn.ofState_op, Assn.comp_op, J_op, stateAt_zero]

theorem post_le : (J N θ ψ hψ).mandNot (bGuard N) ≤ Qpost θ ψ hψ := by
  intro σ
  by_cases hg : bGuard N σ = true
  · exact Assn.op_zero_le (Assn.mandNot_op_of_true (A := J N θ ψ hψ) (b := bGuard N) (σ := σ) hg)
  · have hσ : N ≤ σ := by simpa [bGuard] using hg
    refine le_of_eq ?_
    rw [Assn.mandNot_op_of_false (A := J N θ ψ hψ) (b := bGuard N) (σ := σ) (by simpa using hg),
      J_op, Qpost, Assn.ofState_op, stateAt_of_ge N θ ψ hσ, stateAt_top]

/-- **The Trotter triple** `{ ∣ψ⟩⟨ψ∣ } trotterProg { ∣Rz(θ)ψ⟩⟨Rz(θ)ψ∣ }` is
derivable in `QHL⁺_tot`: exact Hamiltonian simulation of `H = Z` by `N` Trotter
steps, closed by (R-Loop-tot). -/
theorem trotterDeriv : DerivTot (Ppre ψ hψ) (trotterProg N θ) (Qpost θ ψ hψ) :=
  DerivTot.conseq (pre_le N θ ψ hψ)
    (DerivTot.seq (DerivTot.assign (fun _ => 0) (J N θ ψ hψ)) (loopDeriv N θ ψ hψ))
    (post_le N θ ψ hψ)

/-- **The semantic content**, through soundness (L-4): all the mass of a qubit
in `∣ψ⟩` terminates, in `∣Rz(θ)ψ⟩ = ∣e^{-i(θ/2)Z}ψ⟩`. -/
theorem trotterValid : validTot (Ppre ψ hψ) (trotterProg N θ) (Qpost θ ψ hψ) :=
  (trotterDeriv N θ ψ hψ).sound

end

end Qhl.TrotterZ
