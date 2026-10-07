import Mathlib.Analysis.SpecificLimits.Basic
import Qhl.Logic.Soundness

/-!
# The almost-sure-termination loop rule (uniform-contraction / geometric case)

This file provides `validTot_while_ast`: a **semantic** total-correctness rule
for `while` loops whose termination is probabilistic (almost sure) rather than
witnessed by a decreasing integer rank. It is the geometric special case of
quantum almost-sure termination (Ying–Yu–Feng): if the loop body is totally
correct for the invariant `J` and each iteration multiplies the
*loop-continuation* mass `J ∧ b` by a uniform factor `c < 1`, then the residual
mass telescopes geometrically to zero and the loop is totally correct — the
nontermination quantity of the `while` is zero on invariant inputs.

The rule is deliberately **not** a new constructor of `DerivTot`: a loop that
terminates only almost surely is genuinely underivable in the ranked total
system (`DerivTot.whileLoop` demands a ranking function `t : σT → ℕ` that
strictly decreases at *every* iteration), so the rule lives at the `validTot`
level, exactly like `validTot_while` whose stage/exit/limit skeleton it reuses
— only the ranking-based descent is replaced by the geometric decay
`Δₙ₊₁ ≤ c · Δₙ ⇒ Δₙ ≤ cⁿ · Δ₀ → 0`. This file is a port of master's
`rule_loop_ast` (`AlmostSureTermination.lean`) to the CoqQ-branch semantics.

The file is purely **additive**: `Qhl/Logic/Rules.lean`, `Qhl/Logic/Soundness.lean`
and everything under `Qhl/Program/` are untouched, and nothing here is
axiomatized — the geometric-series limit is *proved*
(`ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one` plus `ge_of_tendsto'`).

Contents:

* `Assn.compl` — the effect complement `1 − A` of an assertion, with the two
  mass splits `expectE_add_expectE_compl` (pointwise) and
  `PostH_add_PostH_compl` (run level, `PostH A + PostH Aᶜ = TermH`);
* `LoopBodyContraction` — the uniform-contraction premise;
* `validTot_while_ast` — the rule, and `validTot_while_ast'` its `DerivTot`-fed
  corollary;
* `LoopBodyContraction.of_complement` — a Hoare-style discharge of the
  contraction premise through a *complement* triple (the contraction premise
  upper-bounds a `PostH`, while Hoare reasoning lower-bounds one; the bridge is
  mass conservation).
-/

namespace Qhl

open Finset
open scoped NNReal ENNReal ComplexOrder
open Filter Topology

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## The effect complement of an assertion -/

namespace Assn

/-- The pointwise effect complement `1 − A` of an assertion. It is again an
assertion: `0 ≤ 1 − A` is `A ≤ 1`, and `1 − A ≤ 1` is `0 ≤ A`. -/
noncomputable def compl (A : Assn σT D) : Assn σT D where
  op σ := 1 - A.op σ
  isEffect σ := by
    rw [isEffect_iff]
    refine ⟨(LinearMap.le_def _ _).mp (A.isEffect σ).2, ?_⟩
    rw [sub_sub_cancel]
    exact (A.isEffect σ).isPositive

omit [∀ i, Inhabited (D i)] in
@[simp]
theorem compl_op (A : Assn σT D) (σ : σT) : A.compl.op σ = 1 - A.op σ := rfl

end Assn

omit [∀ i, Inhabited (D i)] in
/-- Trace additivity, pointwise: an assertion and its complement split the mass
of the state (the real-valued form). -/
theorem expect_add_expect_compl (A : Assn σT D) (s : CQState σT D) :
    expect A.op s + expect A.compl.op s = (s.q.mass : ℝ) := by
  rw [expect, expect, Assn.compl_op,
    show s.q.op ∘ₗ (1 - A.op s.cls) = s.q.op - s.q.op ∘ₗ A.op s.cls by
      rw [LinearMap.comp_sub, Module.End.one_eq_id, LinearMap.comp_id],
    map_sub, Complex.sub_re, PDensity.coe_mass]
  ring

/-- The `ℝ≥0∞` form of the pointwise mass split: `⟨A⟩ + ⟨1 − A⟩ = tr ρ`. -/
theorem expectE_add_expectE_compl (A : Assn σT D) (s : CQState σT D) :
    expectE A.op s + expectE A.compl.op s = ((s.q.mass : ℝ≥0) : ℝ≥0∞) := by
  rw [expectE, expectE,
    ← ENNReal.ofReal_add (expect_nonneg (fun σ => A.isPositive σ) s)
      (expect_nonneg (fun σ => A.compl.isPositive σ) s),
    expect_add_expect_compl, ENNReal.ofReal_coe_nnreal]

/-- The run-level mass split: over the terminated histories of a run, an
assertion and its complement collect exactly the terminating mass. -/
theorem PostH_add_PostH_compl (A : Assn σT D) (c : Config σT D) :
    PostH c A.op + PostH c A.compl.op = TermH c := by
  rw [PostH_eq_tsum (fun σ => A.isPositive σ),
    PostH_eq_tsum (fun σ => A.compl.isPositive σ), TermH_eq_tsum, ← ENNReal.tsum_add]
  refine tsum_congr fun n => ?_
  rw [postAtE, postAtE, termMassE, ← dSum_add]
  exact dSum_congr (fun t => expectE_add_expectE_compl A t) c n

/-! ## The uniform-contraction premise -/

/-- Uniform contraction of the loop-continuation mass: from every state whose
classical part satisfies the guard, one full execution of the loop body `P`
returns at most `c` times the invariant mass of the input into states that
*still* satisfy the guard (measured through the terminal-history sum `PostH` of
the guard-masked invariant `J ∧ b`).

For a repeat-until-success loop this is exactly "the retry branch has
probability at most `c` uniformly on the invariant". -/
def LoopBodyContraction (b : σT → Bool) (P : Prog σT D) (J : Assn σT D) (c : ℝ≥0) :
    Prop :=
  ∀ s : CQState σT D, b s.cls = true →
    PostH (Config.init P s) (J.mand b).op ≤ (c : ℝ≥0∞) * expectE J.op s

/-! ## Local copies of the `while` step bridges

`next_init_while_true`/`next_init_while_false` are `private` in
`Qhl/Logic/Soundness.lean`; they are three lines each from the public
`next_init` and `stepProg_while_true`/`stepProg_while_false`. -/

private theorem next_init_while_true' {b : σT → Bool} (P : Prog σT D)
    {s : CQState σT D} (h : b s.cls = true) :
    next (Config.init (.while b P) s) = [(Config.init P s).seqCfg (.while b P)] := by
  rw [next_init, stepProg_while_true b P s.cls s.q h]
  rfl

private theorem next_init_while_false' {b : σT → Bool} (P : Prog σT D)
    {s : CQState σT D} (h : b s.cls = false) :
    next (Config.init (.while b P) s) = [Config.term s] := by
  rw [next_init, stepProg_while_false b P s.cls s.q h]
  rfl

/-- When the guard is false the loop terminates in one step, so the whole
post-expectation is the invariant's expectation in the input state. -/
private theorem PostH_while_of_false {b : σT → Bool} {J : Assn σT D} {P : Prog σT D}
    {s : CQState σT D} (hb : b s.cls = false) :
    PostH (Config.init (.while b P) s) (J.mandNot b).op = expectE J.op s := by
  rw [PostH_of_all_done (Config.isDone_init _ s) (fun c' hc' => ?_)
    fun σ => (J.mandNot b).isPositive σ]
  · rw [next_init_while_false' P hb]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [show (Config.term s).st = s from rfl, expectE_mandNot_of_false (A := J) hb]
  · rw [next_init_while_false' P hb] at hc'
    rw [List.mem_singleton.mp hc']
    rfl

/-! ## The residual sequence and its geometric decay -/

/-- The residual mass still "inside the loop" after `n` iterations: `Δ₀` is the
guard-true invariant mass of the input, and `Δₙ₊₁` accumulates `Δₙ` over the
terminated histories of one body execution (only when the guard holds).

Library-level `Nat` recursion; the ban on `induction` is a rule about example
files, not about the library. -/
private noncomputable def astDelta (b : σT → Bool) (P : Prog σT D) (J : Assn σT D) :
    ℕ → CQState σT D → ℝ≥0∞
  | 0 => fun s => expectE (J.mand b).op s
  | n + 1 => fun s => if b s.cls = true
      then ∑' j, dSum (astDelta b P J n) (Config.init P s) j
      else 0

private theorem astDelta_zero (b : σT → Bool) (P : Prog σT D) (J : Assn σT D)
    (s : CQState σT D) : astDelta b P J 0 s = expectE (J.mand b).op s := rfl

private theorem astDelta_succ (b : σT → Bool) (P : Prog σT D) (J : Assn σT D)
    (n : ℕ) (s : CQState σT D) :
    astDelta b P J (n + 1) s = if b s.cls = true
      then ∑' j, dSum (astDelta b P J n) (Config.init P s) j
      else 0 := rfl

omit [∀ i, Inhabited (D i)] in
/-- Scalar homogeneity of the terminal weight. -/
private theorem dVal_const_mul (x : ℝ≥0∞) (f : CQState σT D → ℝ≥0∞)
    (c : Config σT D) : dVal (fun t => x * f t) c = x * dVal f c := by
  rw [dVal, dVal]
  split
  · rfl
  · rw [mul_zero]

/-- Scalar homogeneity of the frontier sum. -/
private theorem dSum_const_mul (x : ℝ≥0∞) (f : CQState σT D → ℝ≥0∞)
    (c : Config σT D) (n : ℕ) : dSum (fun t => x * f t) c n = x * dSum f c n := by
  simp only [dSum]
  generalize boundedFront c n = l
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih, dVal_const_mul, mul_add]

/-- **Geometric decay**: the uniform contraction premise makes the residual
sequence decay like `cⁿ`. -/
private theorem astDelta_le_pow {b : σT → Bool} {J : Assn σT D} {P : Prog σT D}
    {c : ℝ≥0} (hcontract : LoopBodyContraction b P J c) (n : ℕ) (s : CQState σT D) :
    astDelta b P J n s ≤ (c : ℝ≥0∞) ^ n * expectE (J.mand b).op s := by
  induction n generalizing s with
  | zero => rw [astDelta_zero, pow_zero, one_mul]
  | succ n ih =>
      by_cases hb : b s.cls = true
      · rw [astDelta_succ, if_pos hb]
        calc ∑' j, dSum (astDelta b P J n) (Config.init P s) j
            ≤ ∑' j, dSum (fun t => (c : ℝ≥0∞) ^ n * expectE (J.mand b).op t)
                (Config.init P s) j :=
              ENNReal.tsum_le_tsum fun j => dSum_mono (fun t => ih t) _ j
          _ = (c : ℝ≥0∞) ^ n * ∑' j, dSum (expectE (J.mand b).op) (Config.init P s) j := by
              rw [← ENNReal.tsum_mul_left]
              exact tsum_congr fun j => dSum_const_mul _ _ _ _
          _ = (c : ℝ≥0∞) ^ n * PostH (Config.init P s) (J.mand b).op := by
              rw [PostH_eq_tsum (fun σ => (J.mand b).isPositive σ)]
              rfl
          _ ≤ (c : ℝ≥0∞) ^ n * ((c : ℝ≥0∞) * expectE J.op s) :=
              mul_le_mul' le_rfl (hcontract s hb)
          _ = (c : ℝ≥0∞) ^ (n + 1) * expectE (J.mand b).op s := by
              rw [expectE_mand_of_true hb, pow_succ]
              ring
      · rw [Bool.not_eq_true] at hb
        rw [astDelta_succ, if_neg (by simp [hb])]
        exact zero_le

/-- **The finite-stage bound**: at every stage `n`, the invariant mass of the
input is collected by the loop's terminated histories, up to the residual `Δₙ`.

The guard-false case is the one-step termination of the loop; the guard-true
case unfolds `while b P ⟶ P ; while b P`, applies the body premise, and pushes
the induction hypothesis pointwise under `dSum` through `PostH_seqCfg`. -/
private theorem astStage {b : σT → Bool} {J : Assn σT D} {P : Prog σT D}
    (hbody : validTot (J.mand b) P J) (n : ℕ) (s : CQState σT D) :
    expectE J.op s
      ≤ PostH (Config.init (.while b P) s) (J.mandNot b).op + astDelta b P J n s := by
  induction n generalizing s with
  | zero =>
      by_cases hb : b s.cls = true
      · rw [astDelta_zero, expectE_mand_of_true hb]
        exact le_add_self
      · rw [Bool.not_eq_true] at hb
        exact (le_of_eq (PostH_while_of_false (P := P) (J := J) hb).symm).trans le_self_add
  | succ n ih =>
      by_cases hb : b s.cls = true
      · rw [astDelta_succ, if_pos hb]
        calc expectE J.op s
            = expectE (J.mand b).op s := (expectE_mand_of_true hb).symm
          _ ≤ PostH (Config.init P s) J.op := hbody s
          _ = ∑' j, dSum (expectE J.op) (Config.init P s) j :=
              PostH_eq_tsum (fun σ => J.isPositive σ) _
          _ ≤ ∑' j, dSum (fun t => PostH (Config.init (.while b P) t) (J.mandNot b).op
                + astDelta b P J n t) (Config.init P s) j :=
              ENNReal.tsum_le_tsum fun j => dSum_mono (fun t => ih t) _ j
          _ = (∑' j, dSum (fun t => PostH (Config.init (.while b P) t) (J.mandNot b).op)
                  (Config.init P s) j)
              + ∑' j, dSum (astDelta b P J n) (Config.init P s) j := by
              rw [← ENNReal.tsum_add]
              exact tsum_congr fun j => dSum_add _ _ _ _
          _ = PostH ((Config.init P s).seqCfg (.while b P)) (J.mandNot b).op
              + ∑' j, dSum (astDelta b P J n) (Config.init P s) j := by
              rw [PostH_seqCfg (fun σ => (J.mandNot b).isPositive σ)]
          _ = PostH (Config.init (.while b P) s) (J.mandNot b).op
              + ∑' j, dSum (astDelta b P J n) (Config.init P s) j := by
              rw [PostH_singleton (Config.isDone_init _ s) (next_init_while_true' P hb)
                (fun σ => (J.mandNot b).isPositive σ)]
      · rw [Bool.not_eq_true] at hb
        exact (le_of_eq (PostH_while_of_false (P := P) (J := J) hb).symm).trans le_self_add

/-! ## The rule -/

/-- **(R-Loop-ast)**: the almost-sure-termination loop rule, uniform-contraction
(geometric) case.

If the loop body is totally correct for the invariant (`{J ∧ b} P {J}`) and each
iteration contracts the guard-true invariant mass by a uniform factor `c < 1`,
then the loop is totally correct: `{J} while b do P {J ∧ ¬b}`, with **zero**
nontermination mass on invariant inputs.

This is a `validTot`-level theorem, not a `DerivTot` constructor: the ranked
total system cannot derive a loop that only terminates almost surely. The proof
is the finite-stage bound `astStage` plus the geometric limit `astDelta_le_pow`
— the residual `cⁿ · ⟨J ∧ b⟩` tends to `0` because `⟨J ∧ b⟩` is finite (bounded
by the input mass) and `c < 1`. -/
theorem validTot_while_ast {b : σT → Bool} {J : Assn σT D} {P : Prog σT D}
    (c : ℝ≥0) (hc : c < 1)
    (hbody : validTot (J.mand b) P J)
    (hcontract : LoopBodyContraction b P J c) :
    validTot J (.while b P) (J.mandNot b) := by
  intro s
  -- the residual is finite: it is bounded by the mass of the input state
  have hM : expectE (J.mand b).op s ≠ ∞ :=
    ((expectE_le_mass' (J.mand b) s).trans_lt ENNReal.coe_lt_top).ne
  have hc' : (c : ℝ≥0∞) < 1 := by exact_mod_cast hc
  -- the geometric tail tends to zero, so the stage bounds pass to the limit
  have h0 : Tendsto (fun n : ℕ => (c : ℝ≥0∞) ^ n * expectE (J.mand b).op s) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc') (Or.inr hM)
  have hlim : Tendsto
      (fun n : ℕ => PostH (Config.init (.while b P) s) (J.mandNot b).op
        + (c : ℝ≥0∞) ^ n * expectE (J.mand b).op s) atTop
      (𝓝 (PostH (Config.init (.while b P) s) (J.mandNot b).op)) := by
    simpa using h0.const_add (PostH (Config.init (.while b P) s) (J.mandNot b).op)
  refine ge_of_tendsto' hlim fun n => ?_
  exact (astStage hbody n s).trans (add_le_add le_rfl (astDelta_le_pow hcontract n s))

/-- The paper-shaped corollary: the body premise fed by a genuine `DerivTot`
derivation (the loop itself still lives at the semantic level). -/
theorem validTot_while_ast' {b : σT → Bool} {J : Assn σT D} {P : Prog σT D}
    (c : ℝ≥0) (hc : c < 1) (hbody : DerivTot (J.mand b) P J)
    (hcontract : LoopBodyContraction b P J c) :
    validTot J (.while b P) (J.mandNot b) :=
  validTot_while_ast c hc hbody.sound hcontract

/-! ## Discharging the contraction premise through a complement triple

The contraction premise *upper*-bounds a `PostH`, while Hoare-style reasoning
*lower*-bounds one. The bridge is mass conservation: exhibit a complement
assertion `A'` whose `PostH` is lower-bounded by a derivable triple
`{A'} P {(J ∧ b)ᶜ}`, and the mass split `PostH (J ∧ b) + PostH (J ∧ b)ᶜ = TermH
≤ mass` forces the desired upper bound on the guard-masked `PostH`. -/

/-- Hoare-style discharge of the contraction premise: a total-correctness triple
whose postcondition is the *complement* of the guard-masked invariant, together
with the pointwise lower bound `mass − c · ⟨J⟩ ≤ ⟨A'⟩` on the guard, yields the
uniform contraction. -/
theorem LoopBodyContraction.of_complement {b : σT → Bool} {P : Prog σT D}
    {J : Assn σT D} {c : ℝ≥0} {A' : Assn σT D}
    (hcompl : validTot A' P (J.mand b).compl)
    (hA' : ∀ s : CQState σT D, b s.cls = true →
      ((s.q.mass : ℝ≥0) : ℝ≥0∞) - (c : ℝ≥0∞) * expectE J.op s ≤ expectE A'.op s) :
    LoopBodyContraction b P J c := by
  intro s hb
  have hsum := PostH_add_PostH_compl (J.mand b) (Config.init P s)
  have hTermLe : TermH (Config.init P s) ≤ ((s.q.mass : ℝ≥0) : ℝ≥0∞) :=
    terminatingTraceMass_le (Config.init P s)
  -- the slack is finite, so it can be cancelled on the right
  have hfin : ((s.q.mass : ℝ≥0) : ℝ≥0∞) - (c : ℝ≥0∞) * expectE J.op s ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) tsub_le_self
  refine ENNReal.le_of_add_le_add_right hfin ?_
  calc PostH (Config.init P s) (J.mand b).op
        + (((s.q.mass : ℝ≥0) : ℝ≥0∞) - (c : ℝ≥0∞) * expectE J.op s)
      ≤ PostH (Config.init P s) (J.mand b).op
        + PostH (Config.init P s) (J.mand b).compl.op :=
        add_le_add le_rfl ((hA' s hb).trans (hcompl s))
    _ = TermH (Config.init P s) := hsum
    _ ≤ ((s.q.mass : ℝ≥0) : ℝ≥0∞) := hTermLe
    _ ≤ (c : ℝ≥0∞) * expectE J.op s
        + (((s.q.mass : ℝ≥0) : ℝ≥0∞) - (c : ℝ≥0∞) * expectE J.op s) := by
        rw [add_comm]
        exact le_tsub_add

end Qhl
