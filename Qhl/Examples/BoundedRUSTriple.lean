import Qhl.Logic.HeraldedRUSSource
import Qhl.Gate.PaetznickSvore

/-!
# Bounded Repeat-Until-Success (≤ `N` retries): the Paetznick–Svore instantiation

The bounded repeat-until-success case study, factored as the synthesis
literature factors it: the **generic** bounded-RUS theorem
(`Qhl/Logic/HeraldedRUS.lean`) is instantiated at the **concrete** smallest
circuit of the Paetznick–Svore database (arXiv:1311.1074, Fig. 8: one ancilla,
two `T` gates, two `CNOT`s, three Hadamards —
`Qhl/Gate/PaetznickSvore.lean`). The program, over the store
`(m, k) : Bool × ℕ`:

```
m := 1;  k := 0;
while (m = 1 ∧ k < N) do
  a := ∣0⟩;                    -- reset the ancilla
  (a, t) *= W_PS;              -- the Fig. 8 repeated circuit
  m := M[a];                   -- measure the ancilla (0 = success)
  k := k + 1                   -- one retry spent
od
```

The measurement outcome itself steers the loop: `m = 0` means that the data
wire has undergone the non-Clifford gate `V = (1 + i√2 X)/√3`, while `m = 1`
leaves the data *exactly* unchanged, ready for the next repetition — so no
separate success flag is needed.

## The factoring

The whole quantum content of the example is the **one** branch decomposition
`wPS_decomp`

```
W_PS (∣0⟩ ⊗ χ) = α · ∣0⟩ ⊗ (V χ) + β · ∣1⟩ ⊗ χ,
α = (√3/2)e^{-iπ/4},  β = (1/2)e^{iπ/4},
```

which is precisely the Kraus-operator condition `K₀ = α·V, K₁ = β·1`
(`HeraldedBlock`, with `|α|² + |β|² = 1` *derived* from the unitarity of
`W_PS`). The witness `hbPS` below hands it to the generic theorem; the whole
derivation — invariant, backward chain, ranked loop — is *reused*, never
re-derived. Any other synthesis instantiates the same theorem by exhibiting
its own witness.

## The triple

Using the encoded `QHL⁺_tot` axioms and the source loop rule
`DerivTot.whileLoopSource` with integer variant `t = N − k`: definite
termination, with separate invariant and identity-decrease premises (the unbounded
almost-surely-terminating rendering is the retained `RUSTriple.lean`):

```
⊨tot {1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣}  boundedRusProg N  {J ∧ ¬guard} ,
```

for every unit data ket `ψ₀` and every cap `N`. The postcondition reads
"at exit: **succeeded** — the data wire carries `V ψ₀` — or **exhausted** the
`N` retries, still holding the reset input". Each repetition fails with
probability `|β|² = 1/4`, so the residual all-failure mass after `N`
repetitions is `4^{-N}` — carried by the density operator (the effect
semantics quantifies
over **all** ρ), not stated numerically in the triple. Genuine and non-vacuous
(§4).
-/

namespace Qhl.BoundedRUS

open Qhl Qhl.HeraldedRUS TwoQubits Finset
open scoped ComplexInnerProductSpace ComplexOrder

/-! ## §1. The condition witness: Fig. 8 satisfies the Kraus-operator condition -/

/-- **The instantiation**: the Paetznick–Svore Fig. 8 repeated circuit
satisfies the Kraus-operator condition `K₀ = α·V, K₁ = β·1` — the
single quantum fact of this example, the branch decomposition `wPS_decomp`
handed to the generic bounded-RUS theorem. -/
theorem hbPS : HeraldedBlock wPS vPS alphaPS betaPS := ⟨wPS_decomp⟩

/-- `|α|² = 3/4`: the success probability of one repetition (re-exported from the
gate layer, explanatory — the triple itself does not state it). -/
theorem successProb : ‖alphaPS‖ ^ 2 = 3 / 4 := normSq_alphaPS

/-- `|β|² = 1/4`: the failure probability of one repetition. -/
theorem failProb : ‖betaPS‖ ^ 2 = 1 / 4 := normSq_betaPS

/-- `|α|² + |β|² = 1` — derived from the unitarity of the block through the
condition witness, not assumed. -/
theorem normSq_sum : ‖alphaPS‖ ^ 2 + ‖betaPS‖ ^ 2 = 1 := hbPS.norm_sum

/-! ## §2. The program -/

/-- **The program**: `m := 1; k := 0; while (m = 1 ∧ k < N) do body od`, the
generic `heraldProg` at the Fig. 8 block. -/
noncomputable def boundedRusProg (N : ℕ) : Prog Store D := heraldProg N wPS

/-- The program really is the literal seven-node tree, checked structurally. -/
example (N : ℕ) :
    boundedRusProg N
      = Prog.seq (.assign initM)
          (.seq (.assign initK)
            (.while (guard N)
              (.seq (.init fun _ => regA.sig)
                (.seq (.unitary 2 rAT (gateW wPS))
                  (.seq (.measure 2 1 rA measA updM) (.assign incK)))))) := rfl

/-! ## §3. The headline triple -/

variable {ψ₀ : 𝕢}

/-- **The bounded RUS derivation**, in the encoded system: the
generic derivation — two initialising assignments, then the ranked loop
(`DerivTot.whileLoopSource`, variant `N − k`) — instantiated by the condition
witness `hbPS`. -/
theorem boundedRusDeriv (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) :
    DerivTot (heraldPre ψ₀ hψ₀) (boundedRusProg N)
      ((Jher vPS ψ₀ hψ₀).mandNot (guard N)) :=
  heraldedRusDeriv wPS vPS hψ₀ hbPS N

/-- **The bounded RUS triple**, for every unit data ket `ψ₀` and every cap `N`:

```
⊨tot {1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣}  m:=1; k:=0; while (m=1 ∧ k<N) do … od  {J ∧ ¬guard}
```

with `V = (1 + i√2 X)/√3` inside the postcondition's success branch.
Semantics: the density-matrix / effect one, so this quantifies over **all** ρ.
Termination is **ranked** (variant `N − k`) — closed by `DerivTot.whileLoopSource`,
with no meta / almost-sure rule. -/
theorem boundedRusValid (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) :
    validTot (heraldPre ψ₀ hψ₀) (boundedRusProg N)
      ((Jher vPS ψ₀ hψ₀).mandNot (guard N)) :=
  (boundedRusDeriv hψ₀ N).sound

/-! ## §4. Non-vacuity -/

/-- A concrete input the precondition accepts with all of its mass: the pure
state `∣0⟩ₐ ⊗ ψ₀`, at the armed store `(m, k) = (1, 0)`. -/
noncomputable def inputState (ψ₀ : 𝕢) : CQState Store D :=
  ⟨(true, 0), ⟨outerLM (gv q0 ψ₀) (gv q0 ψ₀), isPositive_outerLM_self _⟩⟩

/-- **The precondition is satisfiable**: it has expectation `1` — the full
mass — in the concrete input state. -/
theorem boundedRusPre_expect_one (hψ₀ : ‖ψ₀‖ = 1) :
    expectE (heraldPre ψ₀ hψ₀).op (inputState ψ₀) = 1 := by
  have h0 : (⟪gv q0 ψ₀, gv q0 ψ₀⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_gv_q0 hψ₀]; norm_num
  have h1 : (⟪gv q1 ψ₀, gv q0 ψ₀⟫ : ℂ) = 0 := by rw [gv_inner, inner_q1_q0, mul_zero]
  rw [expectE, expect, heraldPre_op,
    show (inputState ψ₀).q.op = outerLM (gv q0 ψ₀) (gv q0 ψ₀) from rfl,
    LinearMap.comp_add, map_add, trace_outerLM_comp, trace_outerLM_comp]
  rw [outerLM_apply, outerLM_apply, inner_smul_right, inner_smul_right, h0, h1]
  simp

/-! ## §5. The success-probability triple: `Pr[m = 0] ≥ 1 − 4^{−N}`, formal

The paper's reading "each repetition fails with probability `|β|² = 1/4`, so
the residual all-failure mass after `N` repetitions is `4^{−N}`" was informal
(the
audit's P3). It is now a theorem of the encoded system: the generic
success-probability triple of `Qhl/Logic/HeraldedRUS.lean` §8, instantiated
at the Fig. 8 block — the precondition is the intended-input effect scaled by
`1 − ‖β‖^{2N} = 1 − 4^{−N}` (via `|β|² = 1/4`), the postcondition the
success projector masked by `m = 0`. -/

/-- The failure amplitude is subnormalised, `‖β‖ ≤ 1` — from the derived
normalisation `|α|² + |β|² = 1`. -/
theorem norm_betaPS_le_one : ‖betaPS‖ ≤ 1 := hbPS.norm_b_le_one

/-- **The arithmetic bridge**: the success floor at the Paetznick–Svore block
is `1 − ‖β‖^{2N} = 1 − 4^{−N}`, via `|β|² = 1/4`. -/
theorem succFloor_betaPS (N : ℕ) : succFloor betaPS N = 1 - (1 / 4 : ℝ) ^ N := by
  rw [succFloor, pow_mul, normSq_betaPS]

/-- The success-probability precondition, displayed: the intended-input
effect `1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣` scaled by the constant `1 − 4^{−N}`. -/
theorem successPreQ_op (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) (σ : Store) :
    (heraldPreQ betaPS norm_betaPS_le_one N ψ₀ hψ₀).op σ
      = ((1 - (1 / 4 : ℝ) ^ N : ℝ) : ℂ) •
          (outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀)) := by
  rw [heraldPreQ_op, succFloor_betaPS]

/-- **The success-probability derivation** at the Fig. 8 block: the generic
quantitative derivation (same seven-node tree, quantitative invariant,
ranked loop), instantiated by the condition witness `hbPS`. -/
theorem boundedRusSuccessDeriv (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) :
    DerivTot (heraldPreQ betaPS norm_betaPS_le_one N ψ₀ hψ₀) (boundedRusProg N)
      (succPost vPS ψ₀ hψ₀) :=
  heraldedRusSuccessDeriv wPS vPS norm_betaPS_le_one hψ₀ hbPS N

/-- **The success-probability triple, formal** — the paper's informal
`1 − 4^{−N}` claim internalized (audit P3):

```
⊨tot { (1 − 4^{−N}) · (1ₐ ⊗ ∣ψ₀⟩⟨ψ₀∣) }  boundedRusProg N
     { [m = 0] · ∣0 ⊗ Vψ₀⟩⟨0 ⊗ Vψ₀∣ } ,
```

so on the intended input the loop succeeds (`m = 0`, data wire
carrying `V ψ₀`) with probability at least `1 − 4^{−N}`. The derivation uses
summed measurement, masked-effect consequence, and the source total-loop
rule with variant `N − k`. -/
theorem boundedRusSuccess (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) :
    validTot (heraldPreQ betaPS norm_betaPS_le_one N ψ₀ hψ₀) (boundedRusProg N)
      (succPost vPS ψ₀ hψ₀) :=
  (boundedRusSuccessDeriv hψ₀ N).sound

/-- **Tightness of the constant at the intended input**: the precondition's
expectation in the concrete input state `∣0⟩ₐ ⊗ ψ₀` (armed store) is exactly
`1 − 4^{−N}` — the success-probability floor the triple then guarantees. -/
theorem boundedRusSuccessPre_expect (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) :
    expectE (heraldPreQ betaPS norm_betaPS_le_one N ψ₀ hψ₀).op (inputState ψ₀)
      = ENNReal.ofReal (1 - (1 / 4 : ℝ) ^ N) := by
  have h0 : (⟪gv q0 ψ₀, gv q0 ψ₀⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_gv_q0 hψ₀]; norm_num
  have h1 : (⟪gv q1 ψ₀, gv q0 ψ₀⟫ : ℂ) = 0 := by rw [gv_inner, inner_q1_q0, mul_zero]
  rw [expectE, expect, successPreQ_op hψ₀ N,
    show (inputState ψ₀).q.op = outerLM (gv q0 ψ₀) (gv q0 ψ₀) from rfl,
    LinearMap.comp_smul, map_smul, LinearMap.comp_add, map_add,
    trace_outerLM_comp, trace_outerLM_comp]
  rw [outerLM_apply, outerLM_apply, inner_smul_right, inner_smul_right, h0, h1,
    one_mul, zero_mul, add_zero, smul_eq_mul, mul_one, Complex.ofReal_re]

/-! ## Source-rule derivations of the two bounded triples -/

/-- The first bounded triple in the source system; its measurement selects all outcomes. -/
theorem boundedRusSourceDeriv (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) :
    SourceDerivTot (SourceAssertion.ofAssn (heraldPre ψ₀ hψ₀) (fun _ => True))
      (boundedRusProg N)
      ((sourceInvariant vPS ψ₀ hψ₀).withClassical
        (fun σ => True ∧ guard N σ = false)) :=
  heraldedRusSourceDeriv wPS vPS hψ₀ hbPS N

/-- Soundness of the first source derivation recovers the original semantic triple. -/
theorem boundedRusSourceValid (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) :
    validTot (heraldPre ψ₀ hψ₀) (boundedRusProg N)
      ((Jher vPS ψ₀ hψ₀).mandNot (guard N)) := by
  have hp : ((sourceInvariant vPS ψ₀ hψ₀).withClassical
      (fun σ => True ∧ guard N σ = false)).toAssn =
      (Jher vPS ψ₀ hψ₀).mandNot (guard N) := by
    apply Assn.ext
    funext σ
    by_cases hg : guard N σ = false <;>
      simp [sourceInvariant, SourceAssertion.ofAssn, SourceAssertion.withClassical,
        SourceAssertion.toAssn, Assn.mandNot, Assn.mask, hg] <;> rfl
  simpa only [SourceAssertion.toAssn_ofAssn_true, hp] using
    (boundedRusSourceDeriv hψ₀ N).sound

/-- The quantitative source proof retains the explicit classical success postcondition.
The last failure is omitted because its quantitative effect is zero. -/
theorem boundedRusSuccessSourceDeriv (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) (hN : 0 < N) :
    SourceDerivTot
      (SourceAssertion.ofAssn
        (heraldPreQ betaPS norm_betaPS_le_one N ψ₀ hψ₀) (fun _ => True))
      (boundedRusProg N) (sourceSuccessPost vPS ψ₀ hψ₀) :=
  heraldedRusSuccessSourceDeriv wPS vPS norm_betaPS_le_one hψ₀ hbPS N hN

/-- The second source derivation has the original quantitative semantic interpretation. -/
theorem boundedRusSuccessSourceValid (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) (hN : 0 < N) :
    validTot (heraldPreQ betaPS norm_betaPS_le_one N ψ₀ hψ₀) (boundedRusProg N)
      (succPost vPS ψ₀ hψ₀) := by
  have hp : (sourceSuccessPost vPS ψ₀ hψ₀).toAssn = succPost vPS ψ₀ hψ₀ :=
    SourceAssertion.toAssn_ofAssn _ _
  simpa only [SourceAssertion.toAssn_ofAssn_true, hp] using
    (boundedRusSuccessSourceDeriv hψ₀ N hN).sound


/-! ## Principal triples with a read-only classical bound

The fixed-bound exports above are retained, including the zero-bound semantic
case. These principal source triples use `(N, m, k) : ℕ × (Bool × ℕ)`, require
`N ≥ 1` classically, and use integer rank `N - k` under invariant `k ≤ N`.
-/

noncomputable def boundedRusClassicalProg : Prog ClassicalInput.Store D :=
  ClassicalInput.prog wPS

theorem boundedRusClassical_preserves_bound :
    boundedRusClassicalProg.PreservesParameters Prod.fst :=
  ClassicalInput.preserves_bound wPS

theorem boundedRusClassicalSourceDeriv (hψ₀ : ‖ψ₀‖ = 1) :
    SourceDerivTot (ClassicalInput.pre ψ₀ hψ₀) boundedRusClassicalProg
      (ClassicalInput.post vPS ψ₀ hψ₀) :=
  ClassicalInput.sourceDeriv wPS vPS hψ₀ hbPS

theorem boundedRusClassicalSourceValid (hψ₀ : ‖ψ₀‖ = 1) :
    validTot (ClassicalInput.pre ψ₀ hψ₀).toAssn boundedRusClassicalProg
      (ClassicalInput.post vPS ψ₀ hψ₀).toAssn :=
  (boundedRusClassicalSourceDeriv hψ₀).sound

theorem boundedRusClassicalSuccessSourceDeriv (hψ₀ : ‖ψ₀‖ = 1) :
    SourceDerivTot (ClassicalInput.preQ betaPS norm_betaPS_le_one ψ₀ hψ₀)
      boundedRusClassicalProg (ClassicalInput.postQ vPS ψ₀ hψ₀) :=
  ClassicalInput.sourceDerivQ wPS vPS norm_betaPS_le_one hψ₀ hbPS

theorem boundedRusClassicalSuccessSourceValid (hψ₀ : ‖ψ₀‖ = 1) :
    validTot (ClassicalInput.preQ betaPS norm_betaPS_le_one ψ₀ hψ₀).toAssn
      boundedRusClassicalProg (ClassicalInput.postQ vPS ψ₀ hψ₀).toAssn :=
  (boundedRusClassicalSuccessSourceDeriv hψ₀).sound

/-- The probability coefficient is evaluated at the input store's N. -/
theorem classicalSuccessPreQ_op (hψ₀ : ‖ψ₀‖ = 1) (σ : ClassicalInput.Store) :
    (ClassicalInput.preQ betaPS norm_betaPS_le_one ψ₀ hψ₀).quantum.op σ =
      ((1 - (1 / 4 : ℝ) ^ σ.1 : ℝ) : ℂ) •
        (outerLM (gv q0 ψ₀) (gv q0 ψ₀) + outerLM (gv q1 ψ₀) (gv q1 ψ₀)) :=
  successPreQ_op hψ₀ σ.1 σ.2

end Qhl.BoundedRUS

#print axioms Qhl.BoundedRUS.boundedRusValid
#print axioms Qhl.BoundedRUS.boundedRusDeriv
#print axioms Qhl.BoundedRUS.hbPS
#print axioms Qhl.BoundedRUS.boundedRusPre_expect_one
#print axioms Qhl.BoundedRUS.boundedRusSuccessDeriv
#print axioms Qhl.BoundedRUS.boundedRusSuccess
#print axioms Qhl.BoundedRUS.boundedRusSuccessPre_expect

#print axioms Qhl.BoundedRUS.boundedRusSourceDeriv
#print axioms Qhl.BoundedRUS.boundedRusSourceValid
#print axioms Qhl.BoundedRUS.boundedRusSuccessSourceDeriv
#print axioms Qhl.BoundedRUS.boundedRusSuccessSourceValid

#print axioms Qhl.BoundedRUS.boundedRusClassicalSourceDeriv
#print axioms Qhl.BoundedRUS.boundedRusClassicalSourceValid
#print axioms Qhl.BoundedRUS.boundedRusClassicalSuccessSourceDeriv
#print axioms Qhl.BoundedRUS.boundedRusClassicalSuccessSourceValid
