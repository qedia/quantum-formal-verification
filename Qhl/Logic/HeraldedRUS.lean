import Qhl.Register.TwoQubits
import Qhl.Gate.HeraldedBlock
import Qhl.Logic.UnitaryFull
import Qhl.Logic.Rules
import Qhl.Logic.Soundness
import Qhl.Logic.PreCompute

/-!
# The generic bounded repeat-until-success theorem

The program-logic half of the repeat-until-success decomposition: **any**
two-qubit repeated circuit `W` satisfying the Kraus-operator condition

```
K₀ = a·V,   K₁ = b·1,   |a|² + |b|² = 1        (Qhl/Gate/HeraldedBlock.lean)
```

drives a correct bounded RUS program under the ranked total-correctness loop
rule. The concrete circuit (e.g. the Paetznick–Svore two-`T` Clifford+`T`
block) enters only through the condition; the derivation below never looks
inside `W`.

The program, over the store `(m, k) : Bool × ℕ` — the measurement outcome `m`
(`true` = retry) and the retry counter `k`:

```
m := 1;  k := 0;
while (m = 1 ∧ k < N) do
  a := ∣0⟩;                    -- reset the ancilla
  (a, t) *= W;                 -- the repeated circuit
  m := M[a];                   -- measure the ancilla (0 = success)
  k := k + 1                   -- one retry spent
od
```

The measurement itself writes the classical variable that controls the next
loop iteration: no separate success flag is needed, because the failure branch
of the Kraus-operator condition is the *identity* on the data wire.

## The invariant and the fused backward chain

```
J (m, k) = if m then ∣v₀⟩⟨v₀∣ + ∣v₁⟩⟨v₁∣ else ∣w⟩⟨w∣,
    v_b = ∣b⟩ₐ ⊗ ψ₀,   w = ∣0⟩ₐ ⊗ Vψ₀ .
```

The body chain is (Rule-Meas-sum) exactly as in the bounded RUS example, then the
(Ax-Uni) and (Ax-Init) steps **fused**: pulling the two branch projectors back
through `W` produces rank-ones of *entangled* vectors `tq (W†(∣i⟩ ⊗ ·))`, and
the reset transformer on an arbitrary rank-one (`dualInit_outer_general`,
`Qhl/Register/TwoQubits.lean`) contracts them with the ancilla `∣0⟩` — where
the condition's fused backward laws `ctr0_adjW_succ`/`ctr0_adjW_fail` yield
`star a • ψ₀` and `star b • ψ₀`, so the two contributions recombine to
`(|a|² + |b|²) = 1` times the retry branch of the invariant.

## The theorem

`heraldedRusDeriv` is a derivation in the encoded total-correctness system,
with summed measurement and pointwise order on masked effects: the two initialising assignments,
then the source loop rule
`DerivTot.whileLoopSource` with integer variant `t = N − k` — definite termination, no
meta / semantic loop rule (`PROOF_SYSTEM_ONLY`). `heraldedRusValid` is its
soundness image

```
⊨tot {1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣}  heraldProg N W  {J ∧ ¬guard} ,
```

whose postcondition reads "at exit: **succeeded** — the data wire carries
`V ψ₀` — or **exhausted** the `N` retries, still holding the reset input";
the `|b|^{2N}` residual failure mass is carried by the density operator (the
effect semantics quantifies over all ρ). Any concrete synthesis instantiates
the theorem by exhibiting one `HeraldedBlock` witness.
-/

namespace Qhl.HeraldedRUS

open Qhl TwoQubits Finset
open scoped ComplexInnerProductSpace ComplexOrder

/-! ## §1. The fixture: two qubit cells, the store `(m, k)` -/

/-- The world: the ancilla `false` and the data wire `true`. -/
abbrev L : Type := Bool

/-- Both cells are qubits. -/
abbrev D : L → Type := QubitCells Bool

/-- The classical store `(m, k)`: the last outcome (`true` = retry) and the
retry counter. -/
abbrev Store : Type := Bool × ℕ

/-- The loop guard `m = 1 ∧ k < N`. -/
def guard (N : ℕ) : Store → Bool := fun σ => σ.1 && decide (σ.2 < N)

/-- The ranking function of (R-Loop-tot): the number of retries still
allowed. -/
def rank (N : ℕ) : Store → ℕ := fun σ => N - σ.2

/-- `m := 1` — arm the loop. -/
def initM : Store → Store := fun σ => (true, σ.2)
/-- `k := 0`. -/
def initK : Store → Store := fun σ => (σ.1, 0)
/-- `m := ` the observed bit (outcome `0` = success = exit). -/
def updM : Fin 2 → Store → Store := fun i σ => (finTwoEquiv i, σ.2)
/-- `k := k + 1` — the deterministic decrease of the rank. -/
def incK : Store → Store := fun σ => (σ.1, σ.2 + 1)

@[simp] theorem updM_zero (σ : Store) : updM 0 σ = (false, σ.2) := rfl
@[simp] theorem updM_one (σ : Store) : updM 1 σ = (true, σ.2) := rfl

/-- The one-cell register of the ancilla. -/
abbrev regA : Reg L 1 := Reg.single false

/-- The two-cell register `(a, t)` of the repeated circuit. -/
abbrev regAT : Reg L 2 := Reg.pair false true Bool.false_ne_true

theorem sig_regAT : regAT.sig = (univ : Finset L) := sig_pair_univ

/-- The register expression of the ancilla (constant). -/
abbrev rA : RegExpr Store L 1 := RegExpr.const regA

/-- The register expression of the pair `(a, t)` (constant). -/
abbrev rAT : RegExpr Store L 2 := RegExpr.const regAT

theorem distA (σ : Store) : Function.Injective (rA σ) := regA.inj
theorem distAT (σ : Store) : Function.Injective (rAT σ) := regAT.inj

/-- The ancilla measurement: the promoted store-free layer of
`Qhl/Register/TwoQubits.lean`. -/
noncomputable def measA : ∀ σ : Store, QMeasure 2 (TSpace D (rA σ)) :=
  fun _ => TwoQubits.meas0

/-- The repeated circuit as the gate of the two-cell register: the pair-space
unitary `W`, transported by `tq` to the whole world and read on the register's
tuple space (`Reg.fullGate`, `Qhl/Logic/UnitaryFull.lean`). -/
noncomputable def gateW (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) :
    ∀ σ : Store, UnitaryOp (TSpace D (rAT σ)) :=
  fun _ => regAT.fullGate D sig_regAT (UnitaryOp.congr tq W)

/-! ## §2. The whole-world operator of the repeated circuit -/

/-- The whole-world operator of the repeated circuit: the `tq`-transport of `W`,
with **no residual lift** (`regLift_fullGate` collapses the register
transport). -/
noncomputable def KW (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) :
    EndM D (univ : Finset L) :=
  (UnitaryOp.congr tq W :
    HS D (univ : Finset L) →ₗ[ℂ] HS D (univ : Finset L))

/-- The measurement branch lifts to the promoted whole-world operator. -/
theorem regLift_rA (σ : Store) (h : Function.Injective (rA σ)) (i : Fin 2) :
    regLift (D := D) ⟨rA σ, h⟩ ((measA σ).M i) = TwoQubits.Kmeas i := rfl

/-- The repeated-circuit gate lifts to `KW W` — the linear route through
`regLift_fullGate`, no product-output pair bridge. -/
theorem regLift_rAT (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (σ : Store)
    (h : Function.Injective (rAT σ)) :
    regLift (D := D) ⟨rAT σ, h⟩
        (gateW W σ : TSpace D (⟨rAT σ, h⟩ : Reg L 2).toFun →ₗ[ℂ] _)
      = KW W := by
  change regLift regAT
    (regAT.fullGate D sig_regAT (UnitaryOp.congr tq W) : TSpace D regAT.toFun →ₗ[ℂ] _) = _
  exact regLift_fullGate regAT sig_regAT _

/-- The repeated circuit on a two-wire product state, through the pair space. -/
theorem KW_gv (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (u v : 𝕢) :
    KW W (gv u v)
      = tq ((W : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
          (vpair u v)) := by
  rw [KW, UnitaryOp.congr_apply, tq_symm_gv]

/-- The adjoint of the transported block is the transported adjoint. -/
theorem adjoint_KW (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) :
    LinearMap.adjoint (KW W) = KW (star W) := by
  rw [KW, KW, adjoint_coe_congr]

/-- The adjoint block on a two-wire product state. -/
theorem adjoint_KW_gv (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (u v : 𝕢) :
    LinearMap.adjoint (KW W) (gv u v)
      = tq (LinearMap.adjoint
          (W : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
          (vpair u v)) := by
  rw [adjoint_KW, KW_gv]
  congr 1

/-! ## §3. The program -/

/-- The loop body `a := ∣0⟩; (a,t) *= W; m := M[a]; k := k + 1`. -/
noncomputable def heraldBody (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) :
    Prog Store D :=
  .seq (.init fun _ => regA.sig)
    (.seq (.unitary 2 rAT (gateW W))
      (.seq (.measure 2 1 rA measA updM) (.assign incK)))

/-- **The program**: `m := 1; k := 0; while (m = 1 ∧ k < N) do body od`. -/
noncomputable def heraldProg (N : ℕ) (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) :
    Prog Store D :=
  .seq (.assign initM) (.seq (.assign initK) (.while (guard N) (heraldBody W)))

/-- The program really is the literal seven-node tree, checked structurally. -/
example (N : ℕ) (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) :
    heraldProg N W
      = Prog.seq (.assign initM)
          (.seq (.assign initK)
            (.while (guard N)
              (.seq (.init fun _ => regA.sig)
                (.seq (.unitary 2 rAT (gateW W))
                  (.seq (.measure 2 1 rA measA updM) (.assign incK)))))) := rfl

/-- The assertion obtained by the four atomic axioms for one body. -/
noncomputable def bodyBackward
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (B : Assn Store D) :
    Assn Store D :=
  (((B.comp incK).measurePre rA measA updM).unitaryPre rAT (gateW W)).initPre
    fun _ => regA.sig

/-- One reset, unitary, measurement, and assignment, using their axioms. -/
theorem bodyBackwardDeriv
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (B : Assn Store D) :
    DerivTot (bodyBackward W B) (heraldBody W) B :=
  .seq (.initProg _ _) (.seq (.unitary _ _ _)
    (.seq (.measure _ _ _ _) (.assign incK B)))

/-- Only the two stores produced by the measurement and increment affect the
body's backward assertion at a fixed input store. -/
theorem bodyBackward_op_congr
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (A B : Assn Store D) (σ : Store)
    (h : ∀ i, A.op (incK (updM i σ)) = B.op (incK (updM i σ))) :
    (bodyBackward W A).op σ = (bodyBackward W B).op σ := by
  have hm : ((A.comp incK).measurePre rA measA updM).op σ =
      ((B.comp incK).measurePre rA measA updM).op σ := by
    rw [Assn.measurePre_op_of_dist _ _ _ _ (distA σ),
      Assn.measurePre_op_of_dist _ _ _ _ (distA σ)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Assn.comp_op, h i]
  simp only [bodyBackward, Assn.initPre_op,
    Assn.unitaryPre_op_of_dist _ _ _ (distAT σ), hm]

/-- All mass is preserved by the reset, well-formed unitary and complete
measurement; the assignment also preserves the identity predicate. -/
theorem bodyBackward_one
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) :
    bodyBackward W Assn.one = Assn.one := by
  have hc : (Assn.one : Assn Store D).comp incK = Assn.one := rfl
  have hm : (Assn.one : Assn Store D).measurePre rA measA updM = Assn.one := by
    apply Assn.ext
    exact funext fun σ => Assn.measurePre_one_op (D := D) rA measA updM (distA σ)
  ext σ
  simp only [bodyBackward, hc, hm, Assn.unitaryPre_one _ _ distAT,
    Assn.initPre_one_op, Assn.one_op]

/-- The source rule's identity-predicate decrease premise is independent of
both the data-state invariant and the success-probability weights. -/
theorem bodyIdentityRankDeriv
    (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (N : ℕ) (z : ℤ) :
    DerivTot
      ((Assn.one : Assn Store D).mask fun σ =>
        True ∧ guard N σ = true ∧ (rank N σ : ℤ) = z)
      (heraldBody W)
      ((Assn.one : Assn Store D).mask fun σ => (rank N σ : ℤ) < z) := by
  apply DerivTot.conseq _ (bodyBackwardDeriv W _) (Assn.le_refl' _)
  intro σ
  by_cases hp : True ∧ guard N σ = true ∧ (rank N σ : ℤ) = z
  · have hk : σ.2 < N := by
      by_contra hc
      simp [guard, hc] at hp
    refine Assn.le_op_of_eq_one ?_
    rw [bodyBackward_op_congr W _ Assn.one σ ?_, bodyBackward_one, Assn.one_op]
    intro i
    apply Assn.mask_op_of_pos
    change (↑(N - (σ.2 + 1)) : ℤ) < z
    have hr : (↑(N - σ.2) : ℤ) = z := hp.2.2
    omega
  · exact Assn.op_zero_le (Assn.mask_op_of_neg hp)

/-! ## §4. The invariant -/

section Invariant

variable (V : UnitaryOp 𝕢) (ψ₀ : 𝕢)

/-- The invariant's effect family: on the retry branch (`m = 1`) the effect
`1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣` as an orthogonal sum of two rank-one projectors, on the
success branch (`m = 0`) the projector of `∣0⟩ₐ ⊗ Vψ₀`. -/
noncomputable def Jop (σ : Store) : EndM D (univ : Finset L) :=
  if σ.1 then outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀)
  else outerLM (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀))

variable {ψ₀}

theorem norm_gv_w (hψ₀ : ‖ψ₀‖ = 1) : ‖gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)‖ = 1 :=
  norm_gv norm_q0 (norm_unitaryOp_apply V hψ₀)

/-- The retry branch of the invariant is an effect: the orthogonal sum of two
rank-one projectors. -/
theorem isEffect_retry (hψ₀ : ‖ψ₀‖ = 1) :
    IsEffect (outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀)) :=
  isEffect_add_outerLM_of_orthonormal (norm_gv_q0 hψ₀) (norm_gv_q1 hψ₀) inner_gv_q0_q1

variable (ψ₀)

/-- **The loop invariant.** -/
noncomputable def Jher (hψ₀ : ‖ψ₀‖ = 1) : Assn Store D where
  op := Jop V ψ₀
  isEffect σ := by
    rw [Jop]
    by_cases h : σ.1 = true
    · rw [if_pos h]
      exact isEffect_retry hψ₀
    · rw [Bool.not_eq_true] at h
      rw [if_neg (by simp [h])]
      exact isEffect_outerLM_self (norm_gv_w V hψ₀)

@[simp]
theorem Jher_op (hψ₀ : ‖ψ₀‖ = 1) (σ : Store) : (Jher V ψ₀ hψ₀).op σ = Jop V ψ₀ σ := rfl

theorem Jop_true {σ : Store} (h : σ.1 = true) :
    Jop V ψ₀ σ = outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀) := by
  rw [Jop, if_pos h]

theorem Jop_false {σ : Store} (h : σ.1 = false) :
    Jop V ψ₀ σ
      = outerLM (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) := by
  rw [Jop, if_neg (by simp [h])]

end Invariant

/-! ## §5. The backward chain of the body, for one ranking value `n` -/

section Chains

variable (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (V : UnitaryOp 𝕢)
  {a b : ℂ} {ψ₀ : 𝕢} (hψ₀ : ‖ψ₀‖ = 1)

/-- The postcondition of the measurement inside one pass: the invariant masked
by the decremented rank, pulled back through `k := k + 1`. -/
noncomputable def Binc (N n : ℕ) : Assn Store D :=
  ((Jher V ψ₀ hψ₀).mask fun σ => rank N σ < n).comp incK

/-- The precondition the three quantum axioms derive for `Binc`. -/
noncomputable def bodyPre (N n : ℕ) : Assn Store D :=
  (((Binc V hψ₀ N n).measurePre rA measA updM).unitaryPre rAT (gateW W)).initPre
    fun _ => regA.sig

/-- `Binc` collapses to the invariant operator wherever the decremented rank
mask is met. -/
theorem Binc_op_reduce (N n : ℕ) (τ : Store) (h : rank N (incK τ) < n) :
    (Binc V hψ₀ N n).op τ = Jop V ψ₀ τ := by
  rw [Binc, Assn.comp_op,
    Assn.mask_op_of_pos (A := Jher V ψ₀ hψ₀) (φ := fun σ => rank N σ < n) (σ := incK τ) h]
  rfl

/-- (Rule-Meas-sum): the two branches — the `m = 0` one carries the success
projector, the `m = 1` one the retry effect; the measurement outcome itself
routes the invariant. -/
theorem measurePre_chain (N n : ℕ) (σ : Store)
    (hg : guard N σ = true) (hn : rank N σ = n) :
    ((Binc V hψ₀ N n).measurePre rA measA updM).op σ
      = outerLM (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀))
        + outerLM (gv q1 ψ₀) (gv q1 ψ₀) := by
  have hk : σ.2 < N := by
    by_contra hc
    simp [guard, hc] at hg
  have hn' : N - σ.2 = n := hn
  have hmask0 : rank N (incK (updM 0 σ)) < n := by
    change N - (σ.2 + 1) < n
    omega
  have hmask1 : rank N (incK (updM 1 σ)) < n := by
    change N - (σ.2 + 1) < n
    omega
  rw [Assn.measurePre_op_of_dist _ rA measA updM (distA σ), Fin.sum_univ_two]
  simp only [regLift_rA, TwoQubits.adjoint_Kmeas]
  rw [Binc_op_reduce V hψ₀ N n (updM 0 σ) hmask0,
    Binc_op_reduce V hψ₀ N n (updM 1 σ) hmask1,
    Jop_false V ψ₀ (show (updM 0 σ).1 = false from rfl),
    Jop_true V ψ₀ (show (updM 1 σ).1 = true from rfl)]
  rw [TwoQubits.kmeas_conj_outer, LinearMap.add_comp, LinearMap.comp_add,
    TwoQubits.kmeas_conj_outer, TwoQubits.kmeas_conj_outer, TwoQubits.Kmeas_zero_gv_q0,
    TwoQubits.Kmeas_one_gv_q0, TwoQubits.Kmeas_one_gv_q1, outerLM_zero_left, zero_add]

/-- **(Ax-Uni) and (Ax-Init), fused**: the repeated circuit pulls the two
projectors back to rank-ones of the *entangled* vectors `tq (W†(∣i⟩ ⊗ ·))`,
and the ancilla reset contracts each with `⟨0∣` — where the Kraus-operator
condition collapses the two contributions to `(|a|² + |b|²) = 1` times the
retry branch of the invariant. -/
theorem bodyPre_op (hB : HeraldedBlock W V a b) (N n : ℕ) (σ : Store)
    (hg : guard N σ = true) (hn : rank N σ = n) :
    (bodyPre W V hψ₀ N n).op σ
      = outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀) := by
  rw [bodyPre, Assn.initPre_op,
    Assn.unitaryPre_op_of_dist _ rAT (gateW W) (distAT σ), regLift_rAT,
    measurePre_chain V hψ₀ N n σ hg hn, LinearMap.add_comp, LinearMap.comp_add,
    adjoint_comp_outerLM_comp, adjoint_comp_outerLM_comp, adjoint_KW_gv, adjoint_KW_gv]
  rw [map_add, dualInit_outer_general, dualInit_outer_general,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    hB.ctr0_adjW_succ, hB.ctr0_adjW_fail, adjoint_apply_apply V.isUnitary]
  rw [gv_smul_right, gv_smul_right, gv_smul_right, gv_smul_right,
    outerLM_smul_self, outerLM_smul_self, outerLM_smul_self, outerLM_smul_self,
    ← smul_add, ← smul_add, ← add_smul, star_star, star_star, hB.star_mul_sum, one_smul]

/-! ## §6. The (R-Loop-tot) premise and the loop -/

/-- **The rank-decrease entailment**: on the guard, at ranking value `n`, the
guard-masked invariant entails the body's backward image — because `k := k+1`
deterministically drops the rank below `n`. -/
theorem premise (hB : HeraldedBlock W V a b) (N n : ℕ) :
    ((Jher V ψ₀ hψ₀).mand (guard N)).mask (fun σ => rank N σ = n)
      ≤ bodyPre W V hψ₀ N n := by
  intro σ
  by_cases hn : rank N σ = n
  · by_cases hg : guard N σ = true
    · refine le_of_eq ?_
      rw [Assn.mask_op_of_pos (A := (Jher V ψ₀ hψ₀).mand (guard N))
          (φ := fun σ => rank N σ = n) (σ := σ) hn,
        Assn.mand_op_of_true (A := Jher V ψ₀ hψ₀) (b := guard N) (σ := σ) hg, Jher_op]
      have hm : σ.1 = true := by
        cases h : σ.1 with
        | true => rfl
        | false => simp [guard, h] at hg
      rw [Jop_true V ψ₀ hm]
      exact (bodyPre_op W V hψ₀ hB N n σ hg hn).symm
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := (Jher V ψ₀ hψ₀).mand (guard N))
        (φ := fun σ => rank N σ = n) (σ := σ) hn]
      have hgf : guard N σ = false := by
        cases h : guard N σ with
        | false => rfl
        | true => exact absurd h hg
      exact Assn.mand_op_of_false (A := Jher V ψ₀ hψ₀) (b := guard N) (σ := σ) hgf
  · exact Assn.op_zero_le (Assn.mask_op_of_neg (A := (Jher V ψ₀ hψ₀).mand (guard N))
      (φ := fun σ => rank N σ = n) (σ := σ) hn)

/-- The body premise of (R-Loop-tot) at ranking value `n`: one (R-Conseq)
around the (Ax-Init)+(Ax-Uni)+(Rule-Meas-sum)+(Ax-Ass) chain. -/
theorem bodyDeriv (hB : HeraldedBlock W V a b) (N n : ℕ) :
    DerivTot (((Jher V ψ₀ hψ₀).mand (guard N)).mask fun σ => rank N σ = n)
      (heraldBody W) ((Jher V ψ₀ hψ₀).mask fun σ => rank N σ < n) :=
  DerivTot.conseq (premise W V hψ₀ hB N n)
    (DerivTot.seq (DerivTot.initProg (fun _ => regA.sig) _)
      (DerivTot.seq (DerivTot.unitary rAT (gateW W) _)
        (DerivTot.seq (DerivTot.measure rA measA updM _)
          (DerivTot.assign incK ((Jher V ψ₀ hψ₀).mask fun σ => rank N σ < n)))))
    (Assn.le_refl' _)

/-- The source loop rule's invariant-preservation premise. -/
theorem bodyInvariantDeriv (hB : HeraldedBlock W V a b) (N : ℕ) :
    DerivTot ((Jher V ψ₀ hψ₀).mand (guard N))
      (heraldBody W) (Jher V ψ₀ hψ₀) := by
  apply DerivTot.conseq _ (bodyBackwardDeriv W _) (Assn.le_refl' _)
  intro σ
  by_cases hg : guard N σ = true
  · have hk : σ.2 < N := by
      by_contra hc
      simp [guard, hc] at hg
    have hp := premise W V hψ₀ hB N (rank N σ) σ
    rw [Assn.mask_op_of_pos (φ := fun τ => rank N τ = rank N σ) (σ := σ) rfl] at hp
    apply hp.trans (le_of_eq ?_)
    change (bodyBackward W ((Jher V ψ₀ hψ₀).mask _)).op σ = _
    apply bodyBackward_op_congr
    intro i
    apply Assn.mask_op_of_pos
    change N - (σ.2 + 1) < N - σ.2
    omega
  · exact Assn.op_zero_le (Assn.mand_op_of_false (by simpa using hg))

/-- **(R-Loop-tot)**: separate invariant preservation and identity-predicate
decrease, with the integer cast of `N − k` nonnegative everywhere. -/
theorem loopDeriv (hB : HeraldedBlock W V a b) (N : ℕ) :
    DerivTot (Jher V ψ₀ hψ₀) (.while (guard N) (heraldBody W))
      ((Jher V ψ₀ hψ₀).mandNot (guard N)) := by
  have hmask : (Jher V ψ₀ hψ₀).mask (fun _ => True) = Jher V ψ₀ hψ₀ := by
    ext σ
    simp
  have h := DerivTot.whileLoopSource (A := Jher V ψ₀ hψ₀) (φ := fun _ => True)
    (fun σ => (rank N σ : ℤ)) (fun _ _ => Int.natCast_nonneg _)
    (by simpa only [hmask] using bodyInvariantDeriv W V hψ₀ hB N) (bodyIdentityRankDeriv W N)
  simpa only [hmask] using h

end Chains

/-! ## §7. The generic theorem -/

section Headline

variable (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (V : UnitaryOp 𝕢)
  {a b : ℂ} {ψ₀ : 𝕢} (hψ₀ : ‖ψ₀‖ = 1)

/-- The precondition `1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣`, written as the orthogonal sum of the two
rank-one projectors of `∣0⟩ₐ ⊗ ψ₀` and `∣1⟩ₐ ⊗ ψ₀`: it says nothing about the
ancilla (the program resets it) and pins the data wire to `ψ₀`, uniformly in
the store. -/
noncomputable def heraldPre (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) : Assn Store D where
  op _ := outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀)
  isEffect _ := isEffect_retry hψ₀

@[simp]
theorem heraldPre_op (σ : Store) :
    (heraldPre ψ₀ hψ₀).op σ
      = outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀) := rfl

theorem pre_le : heraldPre ψ₀ hψ₀ ≤ ((Jher V ψ₀ hψ₀).comp initK).comp initM := by
  intro σ
  refine le_of_eq ?_
  rw [heraldPre_op, Assn.comp_op, Assn.comp_op, Jher_op,
    Jop_true V ψ₀ (rfl : (initK (initM σ)).1 = true)]

/-- **The generic bounded-RUS derivation**, in the encoded system with
summed measurement, masked-effect consequence, and the source total-loop rule:
for **any** repeated circuit satisfying the Kraus-operator
condition `K₀ = a·V, K₁ = b·1`, the two initialising assignments followed
by the ranked loop derive

```
⊢ₜ {1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣}  m:=1; k:=0; while (m=1 ∧ k<N) do … od  {J ∧ ¬guard} .
```
-/
theorem heraldedRusDeriv (hB : HeraldedBlock W V a b) (N : ℕ) :
    DerivTot (heraldPre ψ₀ hψ₀) (heraldProg N W)
      ((Jher V ψ₀ hψ₀).mandNot (guard N)) :=
  DerivTot.conseq (pre_le V hψ₀)
    (DerivTot.seq (DerivTot.assign initM ((Jher V ψ₀ hψ₀).comp initK))
      (DerivTot.seq (DerivTot.assign initK (Jher V ψ₀ hψ₀))
        (loopDeriv W V hψ₀ hB N)))
    (Assn.le_refl' _)

/-- **The generic bounded-RUS triple**: any repeated circuit satisfying
the Kraus-operator condition `K₀ = a·V, K₁ = b·1` gives a correct bounded
RUS program under the ranked total-correctness loop rule,

```
⊨tot {1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣}  heraldProg N W  {J ∧ ¬guard} ,
```

for every target gate `V`, unit data ket `ψ₀` and cap `N`. Semantics: the
density-matrix / effect one, quantifying over **all** ρ; termination is ranked
(variant `N − k`), closed by `DerivTot.whileLoopSource` with no meta / almost-sure
rule. -/
theorem heraldedRusValid (hB : HeraldedBlock W V a b) (N : ℕ) :
    validTot (heraldPre ψ₀ hψ₀) (heraldProg N W)
      ((Jher V ψ₀ hψ₀).mandNot (guard N)) :=
  (heraldedRusDeriv W V hψ₀ hB N).sound

end Headline

end Qhl.HeraldedRUS

/-! ## §G. Real-scalar scaling of effects (generic plumbing)

The quantitative success-probability triple below scales effects by real
constants `c ∈ [0, 1]` ("with probability at least `c`"). The closure fact —
a `[0, 1]`-scaled effect is an effect — is generic, so it lives here at the
`Qhl` level, together with the assertion-level combinator `Assn.scale`. -/

namespace Qhl

open scoped ComplexInnerProductSpace ComplexOrder

section EffectScale

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Scaling an effect by a real `c ∈ [0, 1]` yields an effect (both Löwner
bounds via `le_iff_inner_le`). -/
theorem isEffect_real_smul {A : E →ₗ[ℂ] E} (hA : IsEffect A) {c : ℝ}
    (h0 : 0 ≤ c) (h1 : c ≤ 1) : IsEffect ((c : ℂ) • A) := by
  have hpos : ∀ v : E, (0 : ℂ) ≤ ⟪v, A v⟫ := fun v => by
    have h := (le_iff_inner_le (0 : E →ₗ[ℂ] E) A).mp hA.1 v
    rwa [LinearMap.zero_apply, inner_zero_right] at h
  constructor
  · rw [le_iff_inner_le]
    intro v
    rw [LinearMap.zero_apply, inner_zero_right, LinearMap.smul_apply, inner_smul_right]
    exact mul_nonneg (Complex.zero_le_real.mpr h0) (hpos v)
  · rw [le_iff_inner_le]
    intro v
    rw [LinearMap.smul_apply, inner_smul_right, Module.End.one_apply]
    have hle := (le_iff_inner_le A 1).mp hA.2 v
    rw [Module.End.one_apply] at hle
    calc (c : ℂ) * ⟪v, A v⟫
        ≤ 1 * ⟪v, A v⟫ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast h1) (hpos v)
      _ = ⟪v, A v⟫ := one_mul _
      _ ≤ ⟪v, v⟫ := hle

end EffectScale

section AssnScale

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {σT : Type*}

/-- Scaling an assertion by a real `c ∈ [0, 1]` — the effect-valued rendering
of "with probability at least `c` (of the precondition's mass)". -/
noncomputable def Assn.scale (A : Assn σT D) (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    Assn σT D where
  op σ := (c : ℂ) • A.op σ
  isEffect σ := isEffect_real_smul (A.isEffect σ) h0 h1

@[simp]
theorem Assn.scale_op (A : Assn σT D) (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) (σ : σT) :
    (A.scale c h0 h1).op σ = (c : ℂ) • A.op σ := rfl

end AssnScale

end Qhl

/-! ## §8. The success-probability triple

The audit's P3: the reading "the residual all-failure probability after `N`
repetitions is `‖b‖^{2N}`" was informal — carried by the density operator, not
stated by a triple. This section internalizes it, still generically at the
condition level, using summed measurement and masked-effect consequence: the **quantitative
invariant**

```
Jq (m, k) = if m then (1 − ‖b‖^{2(N−k)}) · (1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣)
            else ∣0⟩ₐ⟨0∣ ⊗ ∣Vψ₀⟩⟨Vψ₀∣
```

rides the same ranked loop (variant `N − k`). Per pass, (Rule-Meas-sum) splits the
success branch (coefficient `1`) from the retry branch (coefficient
`1 − ‖b‖^{2(N−k−1)}`), and the fused backward chain recombines them at

```
|a|² · 1 + |b|² · (1 − ‖b‖^{2(N−k−1)}) = 1 − ‖b‖^{2(N−k)}
```

(`succFloor_step`, from the condition's derived `|a|² + |b|² = 1`) — the
invariant telescopes exactly. Entry at `k = 0` gives the scaled precondition
`(1 − ‖b‖^{2N}) · (1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣)`; exit at `m = 0` gives coefficient `1`
into the success projector, and the exhausted branch (`m = 1, k ≥ N`) carries
coefficient `1 − ‖b‖⁰ = 0`, so the postcondition is the success effect masked
by `m = 0`. Soundness then reads, for every input ρ:

```
(1 − ‖b‖^{2N}) · Tr(ρ (1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣)) ≤ E[ [m = 0] · ∣0 ⊗ Vψ₀⟩⟨0 ⊗ Vψ₀∣ ]
                                          ≤ Pr[m = 0 at exit] ,
```

i.e. on the intended (unit-mass, `ψ₀`-sector) input the loop succeeds
with probability at least `1 − ‖b‖^{2N}`. -/

namespace Qhl.HeraldedRUS

open Qhl TwoQubits Finset
open scoped ComplexInnerProductSpace ComplexOrder

/-! ### §8a. The success floor -/

/-- The success floor with `n` retries: `1 − ‖b‖^{2n}`. -/
noncomputable def succFloor (b : ℂ) (n : ℕ) : ℝ := 1 - ‖b‖ ^ (2 * n)

@[simp]
theorem succFloor_zero (b : ℂ) : succFloor b 0 = 0 := by
  simp [succFloor]

theorem succFloor_nonneg {b : ℂ} (hb : ‖b‖ ≤ 1) (n : ℕ) : 0 ≤ succFloor b n := by
  have h := pow_le_one₀ (norm_nonneg b) hb (n := 2 * n)
  simp only [succFloor]
  linarith

theorem succFloor_le_one (b : ℂ) (n : ℕ) : succFloor b n ≤ 1 := by
  have h := pow_nonneg (norm_nonneg b) (2 * n)
  simp only [succFloor]
  linarith

/-! ### §8b. The quantitative invariant -/

section QInvariant

variable (V : UnitaryOp 𝕢) (ψ₀ : 𝕢) (b : ℂ)

/-- The quantitative invariant's effect family: on the retry branch (`m = 1`)
the effect `1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣` scaled by the remaining success floor
`1 − ‖b‖^{2(N−k)}`, on the success branch (`m = 0`) the *unscaled* projector
of `∣0⟩ₐ ⊗ Vψ₀`. -/
noncomputable def JqOp (N : ℕ) (σ : Store) : EndM D (univ : Finset L) :=
  if σ.1 then ((succFloor b (N - σ.2) : ℝ) : ℂ) •
      (outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀))
  else outerLM (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀))

variable {ψ₀ b}

theorem JqOp_true {N : ℕ} {σ : Store} (h : σ.1 = true) :
    JqOp V ψ₀ b N σ
      = ((succFloor b (N - σ.2) : ℝ) : ℂ) •
          (outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀)) := by
  rw [JqOp, if_pos h]

theorem JqOp_false {N : ℕ} {σ : Store} (h : σ.1 = false) :
    JqOp V ψ₀ b N σ
      = outerLM (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) := by
  rw [JqOp, if_neg (by simp [h])]

variable (ψ₀ b)

/-- **The quantitative loop invariant** (an assertion: both branches are
effects, the retry one by `isEffect_real_smul`). -/
noncomputable def Jq (hb : ‖b‖ ≤ 1) (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) : Assn Store D where
  op := JqOp V ψ₀ b N
  isEffect σ := by
    rw [JqOp]
    by_cases h : σ.1 = true
    · rw [if_pos h]
      exact isEffect_real_smul (isEffect_retry hψ₀)
        (succFloor_nonneg hb _) (succFloor_le_one b _)
    · rw [Bool.not_eq_true] at h
      rw [if_neg (by simp [h])]
      exact isEffect_outerLM_self (norm_gv_w V hψ₀)

@[simp]
theorem Jq_op (hb : ‖b‖ ≤ 1) (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) (σ : Store) :
    (Jq V ψ₀ b hb hψ₀ N).op σ = JqOp V ψ₀ b N σ := rfl

end QInvariant

/-! ### §8c. The endpoint assertions -/

/-- **The scaled precondition** `(1 − ‖b‖^{2N}) · (1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣)`: the
intended-input effect of the exact triple, scaled by the success floor. Its
expectation in a state is `(1 − ‖b‖^{2N})` times the intended-input mass. -/
noncomputable def heraldPreQ (b : ℂ) (hb : ‖b‖ ≤ 1) (N : ℕ) (ψ₀ : 𝕢)
    (hψ₀ : ‖ψ₀‖ = 1) : Assn Store D :=
  (heraldPre ψ₀ hψ₀).scale (succFloor b N) (succFloor_nonneg hb N) (succFloor_le_one b N)

theorem heraldPreQ_op (b : ℂ) (hb : ‖b‖ ≤ 1) (N : ℕ) (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1)
    (σ : Store) :
    (heraldPreQ b hb N ψ₀ hψ₀).op σ
      = ((succFloor b N : ℝ) : ℂ) •
          (outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀)) := rfl

/-- **The success postcondition**: the projector of `∣0⟩ₐ ⊗ Vψ₀`, masked by
the classical success flag `m = 0`. Its expectation in an exit state is at
most the probability that `m = 0` there (the effect is below `1`). -/
noncomputable def succPost (V : UnitaryOp 𝕢) (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :
    Assn Store D :=
  Assn.mask
    ⟨fun _ => outerLM (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)),
      fun _ => isEffect_outerLM_self (norm_gv_w V hψ₀)⟩
    fun σ => σ.1 = false

/-! ### §8d. The telescoping backward chain of the body -/

section QChains

variable (W : UnitaryOp (EuclideanSpace ℂ (Bool × Bool))) (V : UnitaryOp 𝕢)
  {a b : ℂ} {ψ₀ : 𝕢} (hb : ‖b‖ ≤ 1) (hψ₀ : ‖ψ₀‖ = 1)

/-- **The telescoping identity**: one pass trades the success weight `|a|²`
at coefficient `1` against the failure weight `|b|²` at the decremented
floor, recovering exactly the current floor —
`|a|² + |b|² (1 − ‖b‖^{2(N−k−1)}) = 1 − ‖b‖^{2(N−k)}`, from the condition's
derived `|a|² + |b|² = 1`. -/
theorem succFloor_step (hB : HeraldedBlock W V a b) {N k : ℕ} (hk : k < N) :
    star a * a + ((succFloor b (N - (k + 1)) : ℝ) : ℂ) * (star b * b)
      = ((succFloor b (N - k) : ℝ) : ℂ) := by
  obtain ⟨n, hn⟩ : ∃ n, N - k = n + 1 := ⟨N - k - 1, by omega⟩
  have hn' : N - (k + 1) = n := by omega
  have hp : ‖b‖ ^ (2 * n) * ‖b‖ ^ 2 = ‖b‖ ^ (2 * (n + 1)) := by
    rw [← pow_add, Nat.mul_succ]
  have hre : ‖a‖ ^ 2 + succFloor b n * ‖b‖ ^ 2 = succFloor b (n + 1) := by
    have hab := hB.norm_sum
    simp only [succFloor]
    linear_combination hab - hp
  rw [hn, hn',
    show (star a * a : ℂ) = ((‖a‖ ^ 2 : ℝ) : ℂ) from by
      rw [show (star a * a : ℂ) = (starRingEnd ℂ) a * a from rfl, RCLike.conj_mul]
      norm_cast,
    show (star b * b : ℂ) = ((‖b‖ ^ 2 : ℝ) : ℂ) from by
      rw [show (star b * b : ℂ) = (starRingEnd ℂ) b * b from rfl, RCLike.conj_mul]
      norm_cast]
  exact_mod_cast hre

/-- The postcondition of the measurement inside one pass: the quantitative
invariant masked by the decremented rank, pulled back through `k := k + 1`. -/
noncomputable def BincQ (N n : ℕ) : Assn Store D :=
  ((Jq V ψ₀ b hb hψ₀ N).mask fun σ => rank N σ < n).comp incK

/-- The precondition the three quantum axioms derive for `BincQ`. -/
noncomputable def bodyPreQ (N n : ℕ) : Assn Store D :=
  (((BincQ V hb hψ₀ N n).measurePre rA measA updM).unitaryPre rAT (gateW W)).initPre
    fun _ => regA.sig

/-- `BincQ` collapses to the invariant operator at the incremented counter
wherever the decremented rank mask is met. -/
theorem BincQ_op_reduce (N n : ℕ) (τ : Store) (h : rank N (incK τ) < n) :
    (BincQ V hb hψ₀ N n).op τ = JqOp V ψ₀ b N (incK τ) := by
  rw [BincQ, Assn.comp_op,
    Assn.mask_op_of_pos (A := Jq V ψ₀ b hb hψ₀ N) (φ := fun σ => rank N σ < n)
      (σ := incK τ) h]
  rfl

/-- (Rule-Meas-sum), quantitatively: the `m = 0` branch carries the success
projector at coefficient `1`, the `m = 1` branch the retry effect at the
*decremented* floor `1 − ‖b‖^{2(N−k−1)}`. -/
theorem measurePreQ_chain (N n : ℕ) (σ : Store)
    (hg : guard N σ = true) (hn : rank N σ = n) :
    ((BincQ V hb hψ₀ N n).measurePre rA measA updM).op σ
      = outerLM (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀))
        + ((succFloor b (N - (σ.2 + 1)) : ℝ) : ℂ) • outerLM (gv q1 ψ₀) (gv q1 ψ₀) := by
  have hk : σ.2 < N := by
    by_contra hc
    simp [guard, hc] at hg
  have hn' : N - σ.2 = n := hn
  have hmask0 : rank N (incK (updM 0 σ)) < n := by
    change N - (σ.2 + 1) < n
    omega
  have hmask1 : rank N (incK (updM 1 σ)) < n := by
    change N - (σ.2 + 1) < n
    omega
  rw [Assn.measurePre_op_of_dist _ rA measA updM (distA σ), Fin.sum_univ_two]
  simp only [regLift_rA, TwoQubits.adjoint_Kmeas]
  rw [BincQ_op_reduce V hb hψ₀ N n (updM 0 σ) hmask0,
    BincQ_op_reduce V hb hψ₀ N n (updM 1 σ) hmask1,
    JqOp_false V (show (incK (updM 0 σ)).1 = false from rfl),
    JqOp_true V (show (incK (updM 1 σ)).1 = true from rfl)]
  simp only [LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_add,
    LinearMap.add_comp]
  rw [TwoQubits.kmeas_conj_outer, TwoQubits.kmeas_conj_outer, TwoQubits.kmeas_conj_outer,
    TwoQubits.Kmeas_zero_gv_q0, TwoQubits.Kmeas_one_gv_q0, TwoQubits.Kmeas_one_gv_q1,
    outerLM_zero_left, zero_add]
  rfl

/-- **(Ax-Uni) and (Ax-Init), fused, quantitatively**: the repeated circuit
pulls the two branch effects back through `W†`, the ancilla reset contracts
them with `⟨0∣` — and the condition's backward laws recombine the coefficients at
`|a|² · 1 + |b|² · (1 − ‖b‖^{2(N−k−1)}) = 1 − ‖b‖^{2(N−k)}`: the invariant
telescopes. -/
theorem bodyPreQ_op (hB : HeraldedBlock W V a b) (N n : ℕ) (σ : Store)
    (hg : guard N σ = true) (hn : rank N σ = n) :
    (bodyPreQ W V hb hψ₀ N n).op σ
      = ((succFloor b (N - σ.2) : ℝ) : ℂ) •
          (outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀)) := by
  have hk : σ.2 < N := by
    by_contra hc
    simp [guard, hc] at hg
  rw [bodyPreQ, Assn.initPre_op,
    Assn.unitaryPre_op_of_dist _ rAT (gateW W) (distAT σ), regLift_rAT,
    measurePreQ_chain V hb hψ₀ N n σ hg hn]
  simp only [LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_add,
    LinearMap.add_comp]
  rw [adjoint_comp_outerLM_comp, adjoint_comp_outerLM_comp, adjoint_KW_gv, adjoint_KW_gv]
  rw [map_add, map_smul, dualInit_outer_general, dualInit_outer_general,
    LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    hB.ctr0_adjW_succ, hB.ctr0_adjW_fail, adjoint_apply_apply V.isUnitary]
  rw [gv_smul_right, gv_smul_right, gv_smul_right, gv_smul_right,
    outerLM_smul_self, outerLM_smul_self, outerLM_smul_self, outerLM_smul_self,
    ← smul_add, ← smul_add, smul_smul, ← add_smul, star_star, star_star,
    succFloor_step W V hB hk]

/-! ### §8e. The (R-Loop-tot) premise and the loop -/

/-- The quantitative rank-decrease entailment: on the guard, at ranking value
`n`, the guard-masked quantitative invariant entails the body's backward
image (an *equality* of effects — the telescoping is exact). -/
theorem premiseQ (hB : HeraldedBlock W V a b) (N n : ℕ) :
    ((Jq V ψ₀ b hb hψ₀ N).mand (guard N)).mask (fun σ => rank N σ = n)
      ≤ bodyPreQ W V hb hψ₀ N n := by
  intro σ
  by_cases hn : rank N σ = n
  · by_cases hg : guard N σ = true
    · refine le_of_eq ?_
      rw [Assn.mask_op_of_pos (A := (Jq V ψ₀ b hb hψ₀ N).mand (guard N))
          (φ := fun σ => rank N σ = n) (σ := σ) hn,
        Assn.mand_op_of_true (A := Jq V ψ₀ b hb hψ₀ N) (b := guard N) (σ := σ) hg,
        Jq_op]
      have hm : σ.1 = true := by
        cases h : σ.1 with
        | true => rfl
        | false => simp [guard, h] at hg
      rw [JqOp_true V hm]
      exact (bodyPreQ_op W V hb hψ₀ hB N n σ hg hn).symm
    · refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := (Jq V ψ₀ b hb hψ₀ N).mand (guard N))
        (φ := fun σ => rank N σ = n) (σ := σ) hn]
      have hgf : guard N σ = false := by
        cases h : guard N σ with
        | false => rfl
        | true => exact absurd h hg
      exact Assn.mand_op_of_false (A := Jq V ψ₀ b hb hψ₀ N) (b := guard N) (σ := σ) hgf
  · exact Assn.op_zero_le (Assn.mask_op_of_neg
      (A := (Jq V ψ₀ b hb hψ₀ N).mand (guard N))
      (φ := fun σ => rank N σ = n) (σ := σ) hn)

/-- The body premise of (R-Loop-tot) at ranking value `n`: one (R-Conseq)
around the (Ax-Init)+(Ax-Uni)+(Rule-Meas-sum)+(Ax-Ass) chain — the same tree as the
exact triple, at the quantitative invariant. -/
theorem bodyDerivQ (hB : HeraldedBlock W V a b) (N n : ℕ) :
    DerivTot (((Jq V ψ₀ b hb hψ₀ N).mand (guard N)).mask fun σ => rank N σ = n)
      (heraldBody W) ((Jq V ψ₀ b hb hψ₀ N).mask fun σ => rank N σ < n) :=
  DerivTot.conseq (premiseQ W V hb hψ₀ hB N n)
    (DerivTot.seq (DerivTot.initProg (fun _ => regA.sig) _)
      (DerivTot.seq (DerivTot.unitary rAT (gateW W) _)
        (DerivTot.seq (DerivTot.measure rA measA updM _)
          (DerivTot.assign incK ((Jq V ψ₀ b hb hψ₀ N).mask fun σ => rank N σ < n)))))
    (Assn.le_refl' _)

/-- The source loop rule's invariant-preservation premise. -/
theorem bodyInvariantDerivQ (hB : HeraldedBlock W V a b) (N : ℕ) :
    DerivTot ((Jq V ψ₀ b hb hψ₀ N).mand (guard N))
      (heraldBody W) (Jq V ψ₀ b hb hψ₀ N) := by
  apply DerivTot.conseq _ (bodyBackwardDeriv W _) (Assn.le_refl' _)
  intro σ
  by_cases hg : guard N σ = true
  · have hk : σ.2 < N := by
      by_contra hc
      simp [guard, hc] at hg
    have hp := premiseQ W V hb hψ₀ hB N (rank N σ) σ
    rw [Assn.mask_op_of_pos (φ := fun τ => rank N τ = rank N σ) (σ := σ) rfl] at hp
    apply hp.trans (le_of_eq ?_)
    change (bodyBackward W ((Jq V ψ₀ b hb hψ₀ N).mask _)).op σ = _
    apply bodyBackward_op_congr
    intro i
    apply Assn.mask_op_of_pos
    change N - (σ.2 + 1) < N - σ.2
    omega
  · exact Assn.op_zero_le (Assn.mand_op_of_false (by simpa using hg))

/-- **(R-Loop-tot)**, quantitatively: `Jq` is preserved separately, while
identity-predicate decrease uses the same proof as the exact triple. -/
theorem loopDerivQ (hB : HeraldedBlock W V a b) (N : ℕ) :
    DerivTot (Jq V ψ₀ b hb hψ₀ N) (.while (guard N) (heraldBody W))
      ((Jq V ψ₀ b hb hψ₀ N).mandNot (guard N)) := by
  have hmask : (Jq V ψ₀ b hb hψ₀ N).mask (fun _ => True) = Jq V ψ₀ b hb hψ₀ N := by
    ext σ
    simp
  have h := DerivTot.whileLoopSource (A := Jq V ψ₀ b hb hψ₀ N) (φ := fun _ => True)
    (fun σ => (rank N σ : ℤ)) (fun _ _ => Int.natCast_nonneg _)
    (by simpa only [hmask] using bodyInvariantDerivQ W V hb hψ₀ hB N) (bodyIdentityRankDeriv W N)
  simpa only [hmask] using h

/-! ### §8f. Entry, exit, and the theorem -/

/-- Entry: the scaled precondition is exactly the invariant at the armed store
`(m, k) = (1, 0)` (floor `1 − ‖b‖^{2N}`). -/
theorem preQ_le (N : ℕ) :
    heraldPreQ b hb N ψ₀ hψ₀ ≤ ((Jq V ψ₀ b hb hψ₀ N).comp initK).comp initM := by
  intro σ
  refine le_of_eq ?_
  rw [heraldPreQ_op, Assn.comp_op, Assn.comp_op, Jq_op,
    JqOp_true V (rfl : (initK (initM σ)).1 = true)]
  rfl

/-- Exit: at `m = 0` the invariant *is* the success projector (coefficient
`1`); at `m = 1` the guard failure forces `k ≥ N`, where the floor is
`1 − ‖b‖⁰ = 0` — the exhausted branch contributes nothing to the success
postcondition.
The exit invariant and the success postcondition are exactly the same
masked operator family. This equality includes stores satisfying the guard:
there both families vanish. It does not assert classical implication from
guard failure to success. -/
theorem exitQ_eq (N : ℕ) :
    (Jq V ψ₀ b hb hψ₀ N).mandNot (guard N) = succPost V ψ₀ hψ₀ := by
  apply Assn.ext
  funext σ
  cases hm : σ.1 with
  | false =>
    have hg : guard N σ = false := by simp [guard, hm]
    rw [Assn.mandNot_op_of_false hg, Jq_op, JqOp_false V hm,
      show (succPost V ψ₀ hψ₀).op σ
          = outerLM (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) (gv q0 ((V : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)) from
        Assn.mask_op_of_pos hm]
  | true =>
    have hs : (succPost V ψ₀ hψ₀).op σ = 0 :=
      Assn.mask_op_of_neg (by simp [hm])
    rw [hs]
    cases hg : guard N σ with
    | true => exact Assn.mandNot_op_of_true hg
    | false =>
      have hk : ¬ σ.2 < N := by simpa [guard, hm] using hg
      rw [Assn.mandNot_op_of_false hg, Jq_op, JqOp_true V hm,
        show N - σ.2 = 0 from by omega, succFloor_zero, Complex.ofReal_zero, zero_smul]

theorem exitQ_le (N : ℕ) :
    (Jq V ψ₀ b hb hψ₀ N).mandNot (guard N) ≤ succPost V ψ₀ hψ₀ := by
  intro σ
  exact le_of_eq (congrArg (fun A : Assn Store D => A.op σ) (exitQ_eq V hb hψ₀ N))

/-- **The generic success-probability derivation**, in the encoded system
with summed measurement, masked-effect consequence, and the source total-loop rule:

```
⊢ₜ { (1 − ‖b‖^{2N}) · (1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣) }
     m := 1; k := 0; while (m = 1 ∧ k < N) do … od
   { [m = 0] · ∣0 ⊗ Vψ₀⟩⟨0 ⊗ Vψ₀∣ } .
```

The same seven-node tree as the exact triple, at the quantitative invariant;
the branch weights combine through (Rule-Meas-sum) and `succFloor_step`.
The final consequence compares masked effects (`exitQ_le`); it does not
assert that the loop's classical exit condition implies success. -/
theorem heraldedRusSuccessDeriv (hB : HeraldedBlock W V a b) (N : ℕ) :
    DerivTot (heraldPreQ b hb N ψ₀ hψ₀) (heraldProg N W) (succPost V ψ₀ hψ₀) :=
  DerivTot.conseq (preQ_le V hb hψ₀ N)
    (DerivTot.seq (DerivTot.assign initM (((Jq V ψ₀ b hb hψ₀ N).comp initK)))
      (DerivTot.seq (DerivTot.assign initK (Jq V ψ₀ b hb hψ₀ N))
        (loopDerivQ W V hb hψ₀ hB N)))
    (exitQ_le V hb hψ₀ N)

/-- **The generic success-probability triple**: for any repeated circuit
satisfying the Kraus-operator condition `K₀ = a·V, K₁ = b·1`,

```
⊨tot { (1 − ‖b‖^{2N}) · (1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣) }  heraldProg N W
     { [m = 0] · ∣0 ⊗ Vψ₀⟩⟨0 ⊗ Vψ₀∣ } .
```

Semantic reading (Def. of `validTot`, over **every** input ρ): the
expectation of the scaled intended-input effect lower-bounds the terminal
expectation of the success-masked projector — and the latter is at most the
terminal probability of `m = 0`. On the intended input (any unit state of the
`ψ₀`-sector, e.g. `∣i⟩ₐ ⊗ ψ₀`), the left side is `1 − ‖b‖^{2N}`, so

```
Pr[m = 0 at exit] ≥ 1 − ‖b‖^{2N} :
```

the audit's informal residual-failure reading, now a theorem obtained by
soundness of the encoded system. -/
theorem heraldedRusSuccessValid (hB : HeraldedBlock W V a b) (N : ℕ) :
    validTot (heraldPreQ b hb N ψ₀ hψ₀) (heraldProg N W) (succPost V ψ₀ hψ₀) :=
  (heraldedRusSuccessDeriv W V hb hψ₀ hB N).sound

end QChains

end Qhl.HeraldedRUS
