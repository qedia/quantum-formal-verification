import Qhl.Logic.Soundness
import Qhl.Logic.ForSeqRule
import Qhl.Register.IsingDiag

/-!
# Trotterized simulation of the diagonal Ising Hamiltonian, as a total-correctness triple

The Hamiltonian-simulation task `e^{-iθH}` for the diagonal `n`-qubit Ising
Hamiltonian

```
H = Σ_{j<n} a j · Z_j + Σ_{j<n-1} b j · Z_j Z_{j+1}
```

by the **first-order Trotter product formula** (the standard product-formula
construction of Hamiltonian simulation; see Nielsen–Chuang §4.7 and the
first-order Trotter/Suzuki literature): split the evolution into `N` equal
slices, and realise each slice by one elementary rotation per Hamiltonian term,

```
i := 0;
while i < N do
  [for j < n   do  q_j        *= Rz (2·(a j)·θ/N)];       -- e^{-i(θ/N)(a j)Z_j}
  [for j < n-1 do  (q_j,q_j+1) *= Rzz (2·(b j)·θ/N)];      -- e^{-i(θ/N)(b j)Z_jZ_{j+1}}
  i := i + 1
od
```

over the classical state `σT = ℕ` (the slice counter) on the standard
`n`-qubit world. Every term of `H` is diagonal in the computational basis, so
all terms **commute** and the first-order product formula is **exact**: `N`
slices compose to `e^{-iθH}` with no Trotter-error term. The correctness
therefore stays entirely inside the printed proof system `QHL⁺_tot` — no
meta-level / almost-sure reasoning and no error analysis. For an arbitrary
`n`-qubit unit ket `ψ` the triple is

```
{ ∣ψ⟩⟨ψ∣ }  trotterIsingProg  { ∣e^{-iθH}ψ⟩⟨e^{-iθH}ψ∣ }.
```

The loop is a genuine ranked `while`, closed by **(R-Loop-tot)**
(`DerivTot.whileLoop`) with ranking function `t i = N − i`; the loop invariant
is "after `i` slices the register is in `e^{-i·θ·min(i,N)/N·H}∣ψ⟩`" (`sAt`,
saturated at `N` exactly as in `TrotterZTriple`). Each slice is a `.seq` of two
`for`-folds whose gates **share wires** (every gate is diagonal on the same
register), so each fold is discharged by the sequential invariant-chain rule
`DerivTot.forProg_finRange_chain` — one (Ax-Uni)+(R-Conseq) rung per gate. The
chain states are the diagonal phases `phaseDiag` of the **partial** Ising
energies `singleE k`/`coupleE k` (`Qhl/Register/IsingDiag.lean`); each rung is
one phase-absorption law (`gateAt_Rz_phaseDiag` / `regLift_Rzz_phaseDiag`) plus
one partial-sum recursion (`singleE_succ` / `coupleE_succ`), and the loop-body
entailment is the angle addition `capAng σ + θ/N = capAng (σ+1)` — the
exactness of the product formula for commuting terms. Everything else is the
proof system: (Ax-Uni), (Ax-Ass), (R-Seq), (R-Conseq) and (R-Loop-tot).
-/

namespace Qhl.TrotterIsing

open Qhl Finset
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal

section

variable (n N : ℕ) [NeZero N] (θ : ℝ) (ca : Fin n → ℝ) (cb : Fin (n - 1) → ℝ)
variable (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1)

/-! ## §1. The program: `N` Trotter slices, one rotation per Hamiltonian term -/

/-- The single-site register expression of the `Rz` gate at site `i`. -/
def regE1 (i : Fin n) : RegExpr ℕ (QubitL n) 1 := fun _ _ => i

/-- The paper's `Dist(q̄)` (eq (2)) is free for a one-cell register. -/
theorem distE1 (i : Fin n) (σ : ℕ) : Function.Injective (regE1 n i σ) :=
  fun x y _ => Subsingleton.elim x y

/-- The slice gate of the single-site term `a i · Z_i`:
`Rz(2·(a i)·θ/N) = e^{-i((a i)θ/N)Z}`, on the tuple space of its register. -/
noncomputable def gate1 (i : Fin n) (σ : ℕ) :
    UnitaryOp (TSpace (QubitD n) (regE1 n i σ)) :=
  singleGate (QubitD n) i (Rz (2 * ca i * (θ / (N : ℝ))))

/-- The two-site register expression of the `Rzz` gate at the coupling `j`. -/
def regE2 (j : Fin (n - 1)) : RegExpr ℕ (QubitL n) 2 :=
  RegExpr.const (Reg.pair (loCell n j) (hiCell n j) (loCell_ne_hiCell n j))

/-- `Dist(q̄)` for the coupling register: the two cells are distinct by
construction. -/
theorem distE2 (j : Fin (n - 1)) (σ : ℕ) : Function.Injective (regE2 n j σ) :=
  (Reg.pair (loCell n j) (hiCell n j) (loCell_ne_hiCell n j)).inj

/-- The slice gate of the coupling term `b j · Z_j Z_{j+1}`:
`Rzz(2·(b j)·θ/N) = e^{-i((b j)θ/N)Z⊗Z}`, on the tuple space of its register. -/
noncomputable def gate2 (j : Fin (n - 1)) (σ : ℕ) :
    UnitaryOp (TSpace (QubitD n) (regE2 n j σ)) :=
  pairGate (D := QubitD n) (loCell n j) (hiCell n j) (loCell_ne_hiCell n j)
    (Rzz (2 * cb j * (θ / (N : ℝ))))

/-- The `Rz` layer of one slice: `[for j < n do q_j *= Rz(2·(a j)·θ/N)]`. -/
noncomputable def rzLayer : Prog ℕ (QubitD n) :=
  [for i < n do [ut i := Rz (2 * ca i * (θ / (N : ℝ)))]]

/-- The `Rzz` layer of one slice:
`[for j < n-1 do (q_j, q_{j+1}) *= Rzz(2·(b j)·θ/N)]`. -/
noncomputable def zzLayer : Prog ℕ (QubitD n) :=
  [for j < n - 1 do
    Prog.unitary2 (loCell n j) (hiCell n j) (loCell_ne_hiCell n j)
      (Rzz (2 * cb j * (θ / (N : ℝ))))]

/-- One first-order Trotter slice: one rotation per Hamiltonian term. -/
noncomputable def slice : Prog ℕ (QubitD n) := (rzLayer n N θ ca).seq (zzLayer n N θ cb)

/-- The loop guard `i < N`. -/
def gd (σ : ℕ) : Bool := decide (σ < N)

/-- The loop body: one slice, then `i := i + 1`. -/
noncomputable def body : Prog ℕ (QubitD n) :=
  (slice n N θ ca cb).seq (Prog.assign fun σ => σ + 1)

/-- The program `i := 0; while i < N do slice; i := i + 1 od`. -/
noncomputable def trotterIsingProg : Prog ℕ (QubitD n) :=
  (Prog.assign fun _ => 0).seq (Prog.while (gd N) (body n N θ ca cb))

/-! ## §2. The interpolating (saturating) states -/

/-- The accumulated evolution angle after `σ` slices, capped at the final
angle `θ`: `θ·(min σ N)/N` (saturated exactly as in `TrotterZTriple`). -/
noncomputable def capAng (σ : ℕ) : ℝ := θ * ((min σ N : ℕ) : ℝ) / (N : ℝ)

/-- The loop-invariant state after `σ` slices: `e^{-i·capAng(σ)·H}∣ψ⟩`. -/
noncomputable def sAt (σ : ℕ) : HS (QubitD n) (univ : Finset (QubitL n)) :=
  (isingEvo n ca cb (capAng N θ σ) :
    HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
      HS (QubitD n) (univ : Finset (QubitL n))) ψ

/-- The chain state at stage `k` of the `Rz` layer of slice `σ+1`: the
invariant phase plus the partial single-site phase of the first `k` gates. -/
noncomputable def chi1 (σ k : ℕ) : HS (QubitD n) (univ : Finset (QubitL n)) :=
  (phaseDiag n
      (fun m => capAng N θ σ * energy n ca cb m + (θ / (N : ℝ)) * singleE n ca k m) :
    HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
      HS (QubitD n) (univ : Finset (QubitL n))) ψ

/-- The chain state at stage `k` of the `Rzz` layer: the full single-site
phase plus the partial coupling phase of the first `k` couplings. -/
noncomputable def chi2 (σ k : ℕ) : HS (QubitD n) (univ : Finset (QubitL n)) :=
  (phaseDiag n
      (fun m => capAng N θ σ * energy n ca cb m
        + (θ / (N : ℝ)) * (singleE n ca n m + coupleE n cb k m)) :
    HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
      HS (QubitD n) (univ : Finset (QubitL n))) ψ

omit [NeZero N] in
include hψ in
theorem norm_sAt (σ : ℕ) : ‖sAt n N θ ca cb ψ σ‖ = 1 := norm_unitaryOp_apply _ hψ

omit [NeZero N] in
include hψ in
theorem norm_chi1 (σ k : ℕ) : ‖chi1 n N θ ca cb ψ σ k‖ = 1 := norm_unitaryOp_apply _ hψ

omit [NeZero N] in
include hψ in
theorem norm_chi2 (σ k : ℕ) : ‖chi2 n N θ ca cb ψ σ k‖ = 1 := norm_unitaryOp_apply _ hψ

omit [NeZero N] in
/-- Stage `0` of the `Rz` layer is the invariant state. -/
theorem chi1_zero (σ : ℕ) : chi1 n N θ ca cb ψ σ 0 = sAt n N θ ca cb ψ σ := by
  simp only [chi1, sAt, isingEvo]
  exact congrArg
    (fun f => (phaseDiag n f : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
      HS (QubitD n) (univ : Finset (QubitL n))) ψ)
    (funext fun m => by rw [singleE_zero]; ring)

omit [NeZero N] in
/-- The exit of the `Rz` layer is the entry of the `Rzz` layer. -/
theorem chi1_top (σ : ℕ) : chi1 n N θ ca cb ψ σ n = chi2 n N θ ca cb ψ σ 0 := by
  simp only [chi1, chi2]
  exact congrArg
    (fun f => (phaseDiag n f : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
      HS (QubitD n) (univ : Finset (QubitL n))) ψ)
    (funext fun m => by rw [coupleE_zero]; ring)

/-! ## §3. The gate computations: one rung per slice gate -/

/-- The `Rz` slice gate at site `i`, extended to the whole world. -/
noncomputable def K1 (i : Fin n) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  gateAt (QubitL n) i (Rz (2 * ca i * (θ / (N : ℝ))))

omit [NeZero N] in
theorem regLift_regE1 (i : Fin n) (σ : ℕ) :
    regLift ⟨regE1 n i σ, distE1 n i σ⟩ (gate1 n N θ ca i σ) = K1 n N θ ca i := rfl

omit [NeZero N] in
theorem isUnitary_K1 (i : Fin n) : IsUnitary (K1 n N θ ca i) :=
  isUnitary_gateAt (QubitL n) i (Rz (2 * ca i * (θ / (N : ℝ))))

/-- The `Rzz` slice gate at coupling `j`, extended to the whole world. -/
noncomputable def K2 (j : Fin (n - 1)) : EndM (QubitD n) (univ : Finset (QubitL n)) :=
  regLift (Reg.pair (loCell n j) (hiCell n j) (loCell_ne_hiCell n j))
    (pairGate (D := QubitD n) (loCell n j) (hiCell n j) (loCell_ne_hiCell n j)
      (Rzz (2 * cb j * (θ / (N : ℝ)))))

omit [NeZero N] in
theorem regLift_regE2 (j : Fin (n - 1)) (σ : ℕ) :
    regLift ⟨regE2 n j σ, distE2 n j σ⟩ (gate2 n N θ cb j σ) = K2 n N θ cb j := rfl

omit [NeZero N] in
theorem isUnitary_K2 (j : Fin (n - 1)) : IsUnitary (K2 n N θ cb j) :=
  isUnitary_regLift _ _

omit [NeZero N] in
/-- **The `Rz` rung**: gate `i` of the `Rz` layer advances the chain one
stage — the phase-absorption law `gateAt_Rz_phaseDiag` plus the partial-sum
recursion `singleE_succ`. -/
theorem chi1_succ (σ : ℕ) (i : Fin n) :
    K1 n N θ ca i (chi1 n N θ ca cb ψ σ (i : ℕ)) = chi1 n N θ ca cb ψ σ ((i : ℕ) + 1) := by
  simp only [chi1, K1]
  rw [gateAt_Rz_phaseDiag]
  exact congrArg
    (fun f => (phaseDiag n f : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
      HS (QubitD n) (univ : Finset (QubitL n))) ψ)
    (funext fun m => by rw [singleE_succ]; ring)

omit [NeZero N] in
/-- **The `Rzz` rung**: coupling gate `j` of the `Rzz` layer advances the
chain one stage — `regLift_Rzz_phaseDiag` plus `coupleE_succ`. -/
theorem chi2_succ (σ : ℕ) (j : Fin (n - 1)) :
    K2 n N θ cb j (chi2 n N θ ca cb ψ σ (j : ℕ)) = chi2 n N θ ca cb ψ σ ((j : ℕ) + 1) := by
  simp only [chi2, K2]
  rw [regLift_Rzz_phaseDiag]
  exact congrArg
    (fun f => (phaseDiag n f : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
      HS (QubitD n) (univ : Finset (QubitL n))) ψ)
    (funext fun m => by rw [coupleE_succ]; ring)

/-- **The slice closes**: the exit of the `Rzz` layer is the invariant state
of the next slice — the angle addition `capAng σ + θ/N = capAng (σ+1)`, i.e.
the exactness of the product formula for commuting terms. -/
theorem chi2_top (σ : ℕ) (hσ : σ < N) :
    chi2 n N θ ca cb ψ σ (n - 1) = sAt n N θ ca cb ψ (σ + 1) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h1 : min σ N = σ := min_eq_left hσ.le
  have h2 : min (σ + 1) N = σ + 1 := min_eq_left (Nat.succ_le_of_lt hσ)
  simp only [chi2, sAt, isingEvo]
  refine congrArg
    (fun f => (phaseDiag n f : HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
      HS (QubitD n) (univ : Finset (QubitL n))) ψ)
    (funext fun m => ?_)
  rw [show singleE n ca n m + coupleE n cb (n - 1) m = energy n ca cb m from rfl]
  simp only [capAng, h1, h2]
  push_cast
  field_simp

omit [NeZero N] in
/-- At `σ = 0` no slice has acted: the state is `∣ψ⟩`. -/
theorem sAt_zero : sAt n N θ ca cb ψ 0 = ψ := by
  rw [sAt,
    show capAng N θ 0 = 0 by simp [capAng]]
  rw [isingEvo,
    show (fun m => (0 : ℝ) * energy n ca cb m) = fun _ => (0 : ℝ) from
      funext fun m => by ring]
  exact phaseDiag_zero_apply n ψ

/-- At `σ = N` the accumulated evolution is the full `e^{-iθH}`. -/
theorem sAt_top :
    sAt n N θ ca cb ψ N
      = (isingEvo n ca cb θ :
          HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
            HS (QubitD n) (univ : Finset (QubitL n))) ψ := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [sAt, show capAng N θ N = θ by rw [capAng, min_self]; field_simp]

omit [NeZero N] in
/-- Beyond `σ = N` the state does not move: the angle is capped at `θ`. -/
theorem sAt_of_ge {σ : ℕ} (h : N ≤ σ) : sAt n N θ ca cb ψ σ = sAt n N θ ca cb ψ N := by
  rw [sAt, sAt,
    show capAng N θ σ = capAng N θ N by rw [capAng, capAng, min_eq_right h, min_self]]

/-! ## §4. The assertions, the loop invariant, and the chain families -/

include hψ in
/-- The loop invariant: "the register is in `e^{-i·capAng(i)·H}∣ψ⟩`". -/
noncomputable def J : Assn ℕ (QubitD n) :=
  ⟨fun σ => outerLM (sAt n N θ ca cb ψ σ) (sAt n N θ ca cb ψ σ),
    fun σ => isEffect_outerLM_self (norm_sAt n N θ ca cb ψ hψ σ)⟩

omit [NeZero N] in
@[simp] theorem J_op (σ : ℕ) :
    (J n N θ ca cb ψ hψ).op σ
      = outerLM (sAt n N θ ca cb ψ σ) (sAt n N θ ca cb ψ σ) := rfl

include hψ in
/-- The stage-`k` assertion of the `Rz`-layer chain. -/
noncomputable def A1 (k : ℕ) : Assn ℕ (QubitD n) :=
  ⟨fun σ => outerLM (chi1 n N θ ca cb ψ σ k) (chi1 n N θ ca cb ψ σ k),
    fun σ => isEffect_outerLM_self (norm_chi1 n N θ ca cb ψ hψ σ k)⟩

omit [NeZero N] in
@[simp] theorem A1_op (k σ : ℕ) :
    (A1 n N θ ca cb ψ hψ k).op σ
      = outerLM (chi1 n N θ ca cb ψ σ k) (chi1 n N θ ca cb ψ σ k) := rfl

include hψ in
/-- The stage-`k` assertion of the `Rzz`-layer chain. -/
noncomputable def A2 (k : ℕ) : Assn ℕ (QubitD n) :=
  ⟨fun σ => outerLM (chi2 n N θ ca cb ψ σ k) (chi2 n N θ ca cb ψ σ k),
    fun σ => isEffect_outerLM_self (norm_chi2 n N θ ca cb ψ hψ σ k)⟩

omit [NeZero N] in
@[simp] theorem A2_op (k σ : ℕ) :
    (A2 n N θ ca cb ψ hψ k).op σ
      = outerLM (chi2 n N θ ca cb ψ σ k) (chi2 n N θ ca cb ψ σ k) := rfl

include hψ in
/-- The precondition "the register is in `∣ψ⟩`". -/
noncomputable def Ppre : Assn ℕ (QubitD n) := Assn.ofState ψ hψ

include hψ in
/-- The postcondition "the register is in `∣e^{-iθH}ψ⟩`". -/
noncomputable def Qpost : Assn ℕ (QubitD n) :=
  Assn.ofState
    ((isingEvo n ca cb θ :
        HS (QubitD n) (univ : Finset (QubitL n)) →ₗ[ℂ]
          HS (QubitD n) (univ : Finset (QubitL n))) ψ)
    (norm_unitaryOp_apply _ hψ)

/-- The ranking function of (R-Loop-tot): the number of slices still to do. -/
def rank (σ : ℕ) : ℕ := N - σ

/-! ## §5. The rung premises: (Ax-Uni) under the loop mask -/

omit [NeZero N] in
/-- The (Ax-Uni)+(R-Conseq) premise of the `Rz` rung at stage `i`, under the
loop's guard-and-rank mask: exactly `chi1_succ`, conjugated. -/
theorem rzPremise (r₀ : ℕ) (i : Fin n) :
    ((A1 n N θ ca cb ψ hψ (i : ℕ)).mand (gd N)).mask (fun σ => rank N σ = r₀)
      ≤ ((((A1 n N θ ca cb ψ hψ ((i : ℕ) + 1)).mand (gd N)).mask
          (fun σ => rank N σ = r₀)).unitaryPre (regE1 n i) (gate1 n N θ ca i)) := by
  intro σ
  by_cases hm : rank N σ = r₀
  · by_cases hg : gd N σ = true
    · refine le_of_eq ?_
      rw [Assn.mask_op_of_pos (A := (A1 n N θ ca cb ψ hψ (i : ℕ)).mand (gd N))
          (φ := fun σ => rank N σ = r₀) (σ := σ) hm,
        Assn.mand_op_of_true (A := A1 n N θ ca cb ψ hψ (i : ℕ)) (b := gd N) (σ := σ) hg,
        Assn.unitaryPre_op_of_dist _ (regE1 n i) (gate1 n N θ ca i) (distE1 n i σ),
        regLift_regE1,
        Assn.mask_op_of_pos (A := (A1 n N θ ca cb ψ hψ ((i : ℕ) + 1)).mand (gd N))
          (φ := fun σ => rank N σ = r₀) (σ := σ) hm,
        Assn.mand_op_of_true (A := A1 n N θ ca cb ψ hψ ((i : ℕ) + 1)) (b := gd N)
          (σ := σ) hg,
        A1_op, A1_op, adjoint_comp_outerLM_comp, ← chi1_succ n N θ ca cb ψ σ i,
        adjoint_apply_apply (isUnitary_K1 n N θ ca i)]
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := (A1 n N θ ca cb ψ hψ (i : ℕ)).mand (gd N))
        (φ := fun σ => rank N σ = r₀) (σ := σ) hm]
      exact Assn.mand_op_of_false (A := A1 n N θ ca cb ψ hψ (i : ℕ)) (b := gd N) (σ := σ)
        (by simpa using hg)
  · exact Assn.op_zero_le (Assn.mask_op_of_neg
      (A := (A1 n N θ ca cb ψ hψ (i : ℕ)).mand (gd N))
      (φ := fun σ => rank N σ = r₀) (σ := σ) hm)

omit [NeZero N] in
/-- The (Ax-Uni)+(R-Conseq) premise of the `Rzz` rung at coupling `j`, under
the loop mask: exactly `chi2_succ`, conjugated. -/
theorem zzPremise (r₀ : ℕ) (j : Fin (n - 1)) :
    ((A2 n N θ ca cb ψ hψ (j : ℕ)).mand (gd N)).mask (fun σ => rank N σ = r₀)
      ≤ ((((A2 n N θ ca cb ψ hψ ((j : ℕ) + 1)).mand (gd N)).mask
          (fun σ => rank N σ = r₀)).unitaryPre (regE2 n j) (gate2 n N θ cb j)) := by
  intro σ
  by_cases hm : rank N σ = r₀
  · by_cases hg : gd N σ = true
    · refine le_of_eq ?_
      rw [Assn.mask_op_of_pos (A := (A2 n N θ ca cb ψ hψ (j : ℕ)).mand (gd N))
          (φ := fun σ => rank N σ = r₀) (σ := σ) hm,
        Assn.mand_op_of_true (A := A2 n N θ ca cb ψ hψ (j : ℕ)) (b := gd N) (σ := σ) hg,
        Assn.unitaryPre_op_of_dist _ (regE2 n j) (gate2 n N θ cb j) (distE2 n j σ),
        regLift_regE2,
        Assn.mask_op_of_pos (A := (A2 n N θ ca cb ψ hψ ((j : ℕ) + 1)).mand (gd N))
          (φ := fun σ => rank N σ = r₀) (σ := σ) hm,
        Assn.mand_op_of_true (A := A2 n N θ ca cb ψ hψ ((j : ℕ) + 1)) (b := gd N)
          (σ := σ) hg,
        A2_op, A2_op, adjoint_comp_outerLM_comp, ← chi2_succ n N θ ca cb ψ σ j,
        adjoint_apply_apply (isUnitary_K2 n N θ cb j)]
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := (A2 n N θ ca cb ψ hψ (j : ℕ)).mand (gd N))
        (φ := fun σ => rank N σ = r₀) (σ := σ) hm]
      exact Assn.mand_op_of_false (A := A2 n N θ ca cb ψ hψ (j : ℕ)) (b := gd N) (σ := σ)
        (by simpa using hg)
  · exact Assn.op_zero_le (Assn.mask_op_of_neg
      (A := (A2 n N θ ca cb ψ hψ (j : ℕ)).mand (gd N))
      (φ := fun σ => rank N σ = r₀) (σ := σ) hm)

/-! ## §6. The layer chains, the slice, and the loop body -/

omit [NeZero N] in
/-- The `Rz` layer, by the sequential invariant-chain rule: one rung per
site. -/
theorem rzChainDeriv (r₀ : ℕ) :
    DerivTot
      (((A1 n N θ ca cb ψ hψ 0).mand (gd N)).mask fun σ => rank N σ = r₀)
      (rzLayer n N θ ca)
      (((A1 n N θ ca cb ψ hψ n).mand (gd N)).mask fun σ => rank N σ = r₀) := by
  refine DerivTot.forProg_finRange_chain
    (fun k => ((A1 n N θ ca cb ψ hψ k).mand (gd N)).mask fun σ => rank N σ = r₀)
    fun i => ?_
  exact DerivTot.conseq (rzPremise n N θ ca cb ψ hψ r₀ i)
    (DerivTot.unitary (regE1 n i) (gate1 n N θ ca i) _) (Assn.le_refl' _)

omit [NeZero N] in
/-- The `Rzz` layer, by the sequential invariant-chain rule: one rung per
coupling. -/
theorem zzChainDeriv (r₀ : ℕ) :
    DerivTot
      (((A2 n N θ ca cb ψ hψ 0).mand (gd N)).mask fun σ => rank N σ = r₀)
      (zzLayer n N θ cb)
      (((A2 n N θ ca cb ψ hψ (n - 1)).mand (gd N)).mask fun σ => rank N σ = r₀) := by
  refine DerivTot.forProg_finRange_chain
    (fun k => ((A2 n N θ ca cb ψ hψ k).mand (gd N)).mask fun σ => rank N σ = r₀)
    fun j => ?_
  exact DerivTot.conseq (zzPremise n N θ ca cb ψ hψ r₀ j)
    (DerivTot.unitary (regE2 n j) (gate2 n N θ cb j) _) (Assn.le_refl' _)

omit [NeZero N] in
/-- One whole slice: the two layer chains glued by (R-Seq) and (R-Conseq)
(the middle assertion is the same state, `chi1_top`). -/
theorem sliceDeriv (r₀ : ℕ) :
    DerivTot
      (((A1 n N θ ca cb ψ hψ 0).mand (gd N)).mask fun σ => rank N σ = r₀)
      (slice n N θ ca cb)
      (((A2 n N θ ca cb ψ hψ (n - 1)).mand (gd N)).mask fun σ => rank N σ = r₀) := by
  have hmid : A1 n N θ ca cb ψ hψ n = A2 n N θ ca cb ψ hψ 0 :=
    Assn.ext (funext fun σ => by rw [A1_op, A2_op, chi1_top])
  refine DerivTot.seq (rzChainDeriv n N θ ca cb ψ hψ r₀) ?_
  refine DerivTot.conseq (fun σ => ?_) (zzChainDeriv n N θ ca cb ψ hψ r₀)
    (Assn.le_refl' _)
  rw [hmid]

/-- The slice exit entails the next invariant, under the mask: `chi2_top`
plus the rank decrease. -/
theorem endPremise (r₀ : ℕ) :
    (((A2 n N θ ca cb ψ hψ (n - 1)).mand (gd N)).mask fun σ => rank N σ = r₀)
      ≤ ((J n N θ ca cb ψ hψ).mask fun σ => rank N σ < r₀).comp fun σ => σ + 1 := by
  intro σ
  by_cases hm : rank N σ = r₀
  · by_cases hg : gd N σ = true
    · have hσ : σ < N := by simpa [gd] using hg
      have hlt : rank N (σ + 1) < r₀ := by simp only [rank] at hm ⊢; omega
      refine le_of_eq ?_
      rw [Assn.mask_op_of_pos (A := (A2 n N θ ca cb ψ hψ (n - 1)).mand (gd N))
          (φ := fun σ => rank N σ = r₀) (σ := σ) hm,
        Assn.mand_op_of_true (A := A2 n N θ ca cb ψ hψ (n - 1)) (b := gd N) (σ := σ) hg,
        Assn.comp_op,
        Assn.mask_op_of_pos (A := J n N θ ca cb ψ hψ)
          (φ := fun σ => rank N σ < r₀) (σ := σ + 1) hlt,
        A2_op, J_op, chi2_top n N θ ca cb ψ σ hσ]
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := (A2 n N θ ca cb ψ hψ (n - 1)).mand (gd N))
        (φ := fun σ => rank N σ = r₀) (σ := σ) hm]
      exact Assn.mand_op_of_false (A := A2 n N θ ca cb ψ hψ (n - 1)) (b := gd N) (σ := σ)
        (by simpa using hg)
  · exact Assn.op_zero_le (Assn.mask_op_of_neg
      (A := (A2 n N θ ca cb ψ hψ (n - 1)).mand (gd N))
      (φ := fun σ => rank N σ = r₀) (σ := σ) hm)

/-- The loop body at ranking value `r₀`: the slice (two chained layers) glued
to `i := i + 1` by (R-Seq), with (R-Conseq) at both ends. -/
theorem bodyDeriv (r₀ : ℕ) :
    DerivTot
      (((J n N θ ca cb ψ hψ).mand (gd N)).mask fun σ => rank N σ = r₀)
      (body n N θ ca cb)
      ((J n N θ ca cb ψ hψ).mask fun σ => rank N σ < r₀) := by
  have h0 : A1 n N θ ca cb ψ hψ 0 = J n N θ ca cb ψ hψ :=
    Assn.ext (funext fun σ => by rw [A1_op, J_op, chi1_zero])
  refine DerivTot.seq
    (DerivTot.conseq (fun σ => ?_) (sliceDeriv n N θ ca cb ψ hψ r₀)
      (endPremise n N θ ca cb ψ hψ r₀))
    (DerivTot.assign (fun σ => σ + 1) ((J n N θ ca cb ψ hψ).mask fun σ => rank N σ < r₀))
  rw [h0]

/-! ## §7. The loop, the triple, and soundness -/

/-- **(R-Loop-tot)**: the invariant `J` with ranking function `rank i = N − i`
— DEFINITE termination, no meta-level rule. -/
theorem loopDeriv :
    DerivTot (J n N θ ca cb ψ hψ)
      (Prog.while (gd N) (body n N θ ca cb))
      ((J n N θ ca cb ψ hψ).mandNot (gd N)) :=
  DerivTot.whileLoop (rank N) (bodyDeriv n N θ ca cb ψ hψ)

omit [NeZero N] in
theorem pre_le : Ppre n ψ hψ ≤ (J n N θ ca cb ψ hψ).comp fun _ => 0 := by
  intro σ
  refine le_of_eq ?_
  rw [Ppre, Assn.ofState_op, Assn.comp_op, J_op, sAt_zero]

theorem post_le : (J n N θ ca cb ψ hψ).mandNot (gd N) ≤ Qpost n θ ca cb ψ hψ := by
  intro σ
  by_cases hg : gd N σ = true
  · exact Assn.op_zero_le
      (Assn.mandNot_op_of_true (A := J n N θ ca cb ψ hψ) (b := gd N) (σ := σ) hg)
  · have hσ : N ≤ σ := by simpa [gd] using hg
    refine le_of_eq ?_
    rw [Assn.mandNot_op_of_false (A := J n N θ ca cb ψ hψ) (b := gd N) (σ := σ)
        (by simpa using hg),
      J_op, Qpost, Assn.ofState_op, sAt_of_ge n N θ ca cb ψ hσ, sAt_top]

/-- **The Trotter–Ising triple**
`{ ∣ψ⟩⟨ψ∣ } trotterIsingProg { ∣e^{-iθH}ψ⟩⟨e^{-iθH}ψ∣ }` is derivable in
`QHL⁺_tot`: exact first-order Trotterized simulation of the diagonal Ising
Hamiltonian by `N` slices, closed by (R-Loop-tot). -/
theorem trotterIsingDeriv :
    DerivTot (Ppre n ψ hψ) (trotterIsingProg n N θ ca cb) (Qpost n θ ca cb ψ hψ) :=
  DerivTot.conseq (pre_le n N θ ca cb ψ hψ)
    (DerivTot.seq (DerivTot.assign (fun _ => 0) (J n N θ ca cb ψ hψ))
      (loopDeriv n N θ ca cb ψ hψ))
    (post_le n N θ ca cb ψ hψ)

/-- **The semantic content**, through soundness (L-4): all the mass of a
register in `∣ψ⟩` terminates, in `∣e^{-iθH}ψ⟩` — over every input density
operator, by the effect semantics of `validTot`. -/
theorem trotterIsingValid :
    validTot (Ppre n ψ hψ) (trotterIsingProg n N θ ca cb) (Qpost n θ ca cb ψ hψ) :=
  (trotterIsingDeriv n N θ ca cb ψ hψ).sound

/-! ## §8. Non-vacuity -/

/-- A concrete input the precondition accepts with all of its mass: the pure
state `∣ψ⟩⟨ψ∣` at counter `0`. -/
noncomputable def inputState : CQState ℕ (QubitD n) :=
  ⟨0, ⟨outerLM ψ ψ, isPositive_outerLM_self ψ⟩⟩

include hψ in
/-- **The precondition is satisfiable**: it has expectation `1` — the full
mass — in the concrete input state, so the triple is not vacuous. -/
theorem trotterIsingPre_expect_one :
    expectE (Ppre n ψ hψ).op (inputState n ψ) = 1 := by
  have hin : (⟪ψ, ψ⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  rw [expectE, expect,
    show (inputState n ψ).q.op = outerLM ψ ψ from rfl,
    show (Ppre n ψ hψ).op (inputState n ψ).cls = outerLM ψ ψ from rfl,
    trace_outerLM_comp, outerLM_apply, inner_smul_right, hin]
  simp

end

end Qhl.TrotterIsing

#print axioms Qhl.TrotterIsing.trotterIsingDeriv
#print axioms Qhl.TrotterIsing.trotterIsingValid
#print axioms Qhl.TrotterIsing.trotterIsingPre_expect_one
