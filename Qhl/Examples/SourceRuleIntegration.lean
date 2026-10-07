import Qhl.Examples.MeasureLoop
import Qhl.Logic.Source.MeasurementAdapters
import Qhl.Logic.Source.LoopGhost

/-! # Concrete uses of the original source rules -/

namespace Qhl.SourceRuleIntegration

open MeasureLoop

/-- A one-qubit assertion over a result bit and an independent outcome ghost. -/
def measuredPost : SourceAssertion (Fin 2 × Fin 2) MeasureLoop.D :=
  SourceAssertion.identity (fun p => p.1 = 1)

/-- A precondition obtained from the source single-outcome axiom, restricted to
an initially zero result bit. -/
noncomputable def measuredPre : SourceAssertion (Fin 2 × Fin 2) MeasureLoop.D :=
  (measuredPost.measureOutcomePreSource
    (fun p => MeasureLoop.rq (finTwoEquiv p.1))
    (fun p => MeasureLoop.meas (finTwoEquiv p.1))
    SourceVariable.fst.set SourceVariable.snd.get).withClassical
      (fun p => p.2 = 1 ∧ p.1 = 0)

/-- The existing computational-basis measurement, now on an ordinary result
bit paired with a fresh outcome bit. -/
noncomputable def measuredProgram : Prog (Fin 2 × Fin 2) MeasureLoop.D :=
  .measure 2 1 (fun p => MeasureLoop.rq (finTwoEquiv p.1))
    (fun p => MeasureLoop.meas (finTwoEquiv p.1)) SourceVariable.fst.set

/-- Read the result bit as the original Boolean store and preserve the
independent outcome ghost on writes. -/
def measuredLens : StoreLens (Fin 2 × Fin 2) Bool where
  get p := finTwoEquiv p.1
  put p b := (finTwoEquiv.symm b, p.2)

/-- The concrete source example executes precisely the transported
computational-basis measurement from `MeasureLoop`. -/
theorem measuredProgram_eq_mapStore :
    measuredProgram = MeasureLoop.body.mapStore measuredLens := by
  simp [measuredProgram, MeasureLoop.body, Prog.mapStore, measuredLens,
    MeasureLoop.upd, SourceVariable.fst]

/-- The measurement proof uses the derived single-outcome rule and
source consequence to restrict input and forget the ghost equality on output. -/
theorem measuredDeriv : SourceDerivTot measuredPre measuredProgram measuredPost := by
  let r : RegExpr (Fin 2 × Fin 2) MeasureLoop.L 1 :=
    fun p => MeasureLoop.rq (finTwoEquiv p.1)
  let M : ∀ p, QMeasure 2 (TSpace MeasureLoop.D (r p)) :=
    fun p => MeasureLoop.meas (finTwoEquiv p.1)
  let pre := measuredPost.measureOutcomePreSource r M
    SourceVariable.fst.set SourceVariable.snd.get
  let post := measuredPost.measureOutcomePostSource
    SourceVariable.fst.get SourceVariable.snd.get
  have hpre : SourceAssertion.Entails measuredPre pre := by
    constructor
    · intro p hp
      exact hp.1
    · intro p _
      exact ⟨Iff.rfl, fun _ => le_rfl⟩
  have hpost : SourceAssertion.Entails post measuredPost := by
    constructor
    · intro p hp
      exact hp.1
    · intro p _
      exact ⟨Iff.rfl, fun _ => le_rfl⟩
  change SourceDerivTot measuredPre (.measure 2 1 r M SourceVariable.fst.set)
    measuredPost
  exact SourceDerivTot.conseq hpre
    (SourceDerivTot.measure r M SourceVariable.fst SourceVariable.snd measuredPost
      SourceVariable.independent_fst_snd
      (SourceAssertion.withGhost_fresh
        (SourceAssertion.identity (D := MeasureLoop.D) (fun i : Fin 2 => i = 1))
        (Fin 2)) (fun _ _ _ _ => trivial)) hpost

/-- Semantic total correctness of the source-derived basis measurement. -/
theorem measuredValid : validTot measuredPre.toAssn measuredProgram measuredPost.toAssn :=
  measuredDeriv.sound

/-- The invariant of a counter that starts at zero and increments to `N`. -/
def countInv (N : ℕ) : SourceAssertion ℕ MeasureLoop.D :=
  SourceAssertion.identity (fun n => n ≤ N)

/-- The counted loop body increments the ordinary counter. -/
def countBody : Prog ℕ MeasureLoop.D := .assign Nat.succ

/-- The counted while program with a literal bound `N`. -/
def countLoop (N : ℕ) : Prog ℕ MeasureLoop.D :=
  .while (fun n => decide (n < N)) countBody

/-- The source invariant is preserved by incrementing while below `N`. -/
private theorem countBodyInv (N : ℕ) : SourceDerivTot
    ((countInv N).withClassical
      (fun n => (countInv N).classical n ∧ decide (n < N) = true))
    countBody (countInv N) := by
  have hpre : SourceAssertion.Entails
      ((countInv N).withClassical
        (fun n => (countInv N).classical n ∧ decide (n < N) = true))
      ((countInv N).subst Nat.succ) := by
    constructor
    · intro n hn
      change n + 1 ≤ N
      have hlt : n < N := by simpa using hn.2
      omega
    · intro n _
      exact ⟨Iff.rfl, fun _ => le_rfl⟩
  change SourceDerivTot _ (.assign Nat.succ) _
  exact SourceDerivTot.conseq hpre
    (SourceDerivTot.assign Nat.succ (countInv N))
    (SourceAssertion.entails_refl _)

/-- The ghost rank strictly decreases after one counter increment. -/
private theorem countBodyRank (N : ℕ) : SourceDerivTot
    ((countInv N).rankGhostPre (fun n => decide (n < N))
      (fun n => (N : Int) - n))
    (countBody.mapStore (StoreLens.fst (R := Int)))
    (SourceAssertion.rankGhostPost (D := MeasureLoop.D) (σT := ℕ)
      (fun n => (N : Int) - n)) := by
  let f : ℕ × Int → ℕ × Int := fun p => (p.1 + 1, p.2)
  let post := SourceAssertion.rankGhostPost (D := MeasureLoop.D) (σT := ℕ)
    (fun n => (N : Int) - n)
  have hpre : SourceAssertion.Entails
      ((countInv N).rankGhostPre (fun n => decide (n < N))
        (fun n => (N : Int) - n)) (post.subst f) := by
    constructor
    · intro p hp
      change (N : Int) - (p.1 + 1 : ℕ) < p.2
      have hr : (N : Int) - p.1 = p.2 := hp.2.2
      omega
    · intro p _
      exact ⟨Iff.rfl, fun _ => le_rfl⟩
  change SourceDerivTot _ (.assign f) post
  exact SourceDerivTot.conseq hpre (SourceDerivTot.assign f post)
    (SourceAssertion.entails_refl _)

/-- The literal source total-loop rule proves every finite bound, including zero. -/
theorem countLoopDeriv (N : ℕ) : SourceDerivTot
    (countInv N) (countLoop N)
    (SourceAssertion.identity (D := MeasureLoop.D) (fun n => n = N)) := by
  have hbound : ∀ n, (countInv N).classical n →
      0 ≤ (N : Int) - n := by
    intro n hn
    change n ≤ N at hn
    omega
  have hloop := SourceDerivTot.whileLoopGhost
    (A := countInv N) (P := countBody)
    (fun n => decide (n < N)) (fun n => (N : Int) - n)
    hbound (countBodyInv N) (countBodyRank N)
  have hpost : SourceAssertion.Entails
      ((countInv N).withClassical
        (fun n => (countInv N).classical n ∧ decide (n < N) = false))
      (SourceAssertion.identity (D := MeasureLoop.D) (fun n => n = N)) := by
    constructor
    · intro n hn
      have hle : n ≤ N := hn.1
      have hnot : ¬ n < N := by simpa using hn.2
      exact Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
    · intro n _
      exact ⟨Iff.rfl, fun _ => le_rfl⟩
  change SourceDerivTot (countInv N) (.while (fun n => decide (n < N)) countBody) _
  exact SourceDerivTot.conseq (SourceAssertion.entails_refl _) hloop hpost

/-- Semantic total correctness follows from the literal source derivation. -/
theorem countLoopValid (N : ℕ) : validTot (countInv N).toAssn
    (countLoop N)
    (SourceAssertion.identity (D := MeasureLoop.D) (fun n => n = N)).toAssn :=
  (countLoopDeriv N).sound

/-- The library's counted program with a no-op user body starts at zero,
increments its counter, and stops at the given bound. -/
def countedProgram (N : ℕ) : Prog ℕ MeasureLoop.D :=
  countedProg CounterLens.nat (fun _ => N) .skip

/-- The complete counted program is derivable using the literal source loop
with a fresh integer rank variable, including when the bound is zero. -/
theorem countedProgramDeriv (N : ℕ) : SourceDerivTot
    (SourceAssertion.identity (D := MeasureLoop.D) (fun _ : ℕ => True))
    (countedProgram N)
    (SourceAssertion.identity (D := MeasureLoop.D) (fun n => n = N)) := by
  let b : ℕ → Bool := fun n => decide (n < N)
  let body : Prog ℕ MeasureLoop.D := .seq .skip countBody
  have hInv : SourceDerivTot
      ((countInv N).withClassical
        (fun n => (countInv N).classical n ∧ b n = true)) body (countInv N) :=
    SourceDerivTot.seq (SourceDerivTot.skip _) (countBodyInv N)
  have hRank : SourceDerivTot
      ((countInv N).rankGhostPre b (fun n => (N : Int) - n))
      (body.mapStore (StoreLens.fst (R := Int)))
      (SourceAssertion.rankGhostPost (D := MeasureLoop.D)
        (fun n => (N : Int) - n)) := by
    change SourceDerivTot _ (.seq .skip
      (countBody.mapStore (StoreLens.fst (R := Int)))) _
    exact SourceDerivTot.seq (SourceDerivTot.skip _) (countBodyRank N)
  have hbound : ∀ n, (countInv N).classical n → 0 ≤ (N : Int) - n := by
    intro n hn
    change n ≤ N at hn
    omega
  have hloop := SourceDerivTot.whileLoopGhost
    (A := countInv N) (P := body) b (fun n => (N : Int) - n)
    hbound hInv hRank
  have hpost : SourceAssertion.Entails
      ((countInv N).withClassical
        (fun n => (countInv N).classical n ∧ b n = false))
      (SourceAssertion.identity (D := MeasureLoop.D) (fun n => n = N)) := by
    constructor
    · intro n hn
      have hle : n ≤ N := hn.1
      have hnot : ¬ n < N := by simpa [b] using hn.2
      exact Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
    · intro n _
      exact ⟨Iff.rfl, fun _ => le_rfl⟩
  have hwhile : SourceDerivTot (countInv N) (.while b body)
      (SourceAssertion.identity (D := MeasureLoop.D) (fun n => n = N)) :=
    SourceDerivTot.conseq (SourceAssertion.entails_refl _) hloop hpost
  let f : ℕ → ℕ := fun _ => 0
  have hinitPre : SourceAssertion.Entails
      (SourceAssertion.identity (D := MeasureLoop.D) (fun _ : ℕ => True))
      ((countInv N).subst f) := by
    constructor
    · intro n _
      change 0 ≤ N
      exact Nat.zero_le N
    · intro n _
      exact ⟨Iff.rfl, fun _ => le_rfl⟩
  have hinit : SourceDerivTot
      (SourceAssertion.identity (D := MeasureLoop.D) (fun _ : ℕ => True))
      (.assign f) (countInv N) :=
    SourceDerivTot.conseq hinitPre (SourceDerivTot.assign f (countInv N))
      (SourceAssertion.entails_refl _)
  change SourceDerivTot _ (.seq (.assign f) (.while b body)) _
  exact SourceDerivTot.seq hinit hwhile

/-- The source derivation proves termination and the exact final count. -/
theorem countedProgramValid (N : ℕ) : validTot
    (SourceAssertion.identity (D := MeasureLoop.D) (fun _ : ℕ => True)).toAssn
    (countedProgram N)
    (SourceAssertion.identity (D := MeasureLoop.D) (fun n => n = N)).toAssn :=
  (countedProgramDeriv N).sound

/-- Identity assertion on a result and counter store. -/
def selectedIdentity : SourceAssertion (Fin 2 × ℕ) MeasureLoop.D :=
  SourceAssertion.identity (fun _ => True)

/-- All outcomes preserve the identity effect by measurement completeness. -/
theorem selectedAll_identity_op (σ : Fin 2 × ℕ) :
    (selectedIdentity.measureSelectedPreSource (fun _ => MeasureLoop.rq false)
        (fun _ => MeasureLoop.meas false) SourceVariable.fst.set
        (fun _ _ => true)).quantum.op σ = 1 := by
  simpa [selectedIdentity, SourceAssertion.measureSelectedPreSource, SourceAssertion.identity,
    Assn.measurePre, Assn.one, MeasureLoop.distQ false] using
    (Assn.measurePre_one_op (D := MeasureLoop.D)
      (σT := Fin 2 × ℕ) (fun _ => MeasureLoop.rq false)
      (fun _ => MeasureLoop.meas false) SourceVariable.fst.set
      (σ := σ) (MeasureLoop.distQ false))

/-- Selecting every outcome proves preservation of the full identity assertion. -/
theorem selectedAllDeriv : SourceDerivTot selectedIdentity
    (.measure 2 1 (fun _ => MeasureLoop.rq false)
      (fun _ => MeasureLoop.meas false) SourceVariable.fst.set) selectedIdentity := by
  apply SourceDerivTot.conseq _
    (SourceDerivTot.measureSelected (fun _ => MeasureLoop.rq false)
      (fun _ => MeasureLoop.meas false) SourceVariable.fst (fun _ _ => true)
      selectedIdentity (fun _ _ => rfl) (fun _ _ _ _ => trivial)) _
  · constructor
    · intro σ _ i _
      trivial
    · intro σ _
      constructor
      · exact ⟨fun _ => ⟨MeasureLoop.distQ false, fun _ _ => trivial⟩, fun _ => trivial⟩
      · intro _
        rw [selectedAll_identity_op]
        exact le_rfl
  · constructor
    · intro σ _
      trivial
    · intro σ _
      exact ⟨Iff.rfl, fun _ => le_rfl⟩

/-- A selector may depend on an unchanged counter and admit both outcomes
before the last attempt, while retaining only success on the last attempt. -/
def attemptSelector (σ : Fin 2 × ℕ) (i : Fin 2) : Bool :=
  decide (σ.2 < 3 ∨ i = 0)

/-- A concrete store-dependent selected measurement uses the same source rule. -/
theorem selectedAttemptDeriv :
    SourceDerivTot
      (selectedIdentity.measureSelectedPreSource (fun _ => MeasureLoop.rq false)
          (fun _ => MeasureLoop.meas false) SourceVariable.fst.set attemptSelector)
      (.measure 2 1 (fun _ => MeasureLoop.rq false)
        (fun _ => MeasureLoop.meas false) SourceVariable.fst.set)
      (selectedIdentity.measureSelectedPostSource SourceVariable.fst.get attemptSelector) :=
  .measureSelected _ _ SourceVariable.fst attemptSelector _ (fun _ _ => rfl)
    (fun _ _ _ _ => trivial)

/-- The generalized selector proof compiles through source-rule soundness. -/
theorem selectedAttemptValid :
    validTot
      (selectedIdentity.measureSelectedPreSource (fun _ => MeasureLoop.rq false)
          (fun _ => MeasureLoop.meas false) SourceVariable.fst.set attemptSelector).toAssn
      (.measure 2 1 (fun _ => MeasureLoop.rq false)
        (fun _ => MeasureLoop.meas false) SourceVariable.fst.set)
      (selectedIdentity.measureSelectedPostSource SourceVariable.fst.get attemptSelector).toAssn :=
  selectedAttemptDeriv.sound

/-! Scalar convex rules at subnormalized weights, exercised on actual source proofs. -/
open scoped NNReal

private noncomputable def quarterWeights (_ : Fin 2) : ℝ≥0 := 1 / 4
private theorem quarterWeights_sum : ∑ i, quarterWeights i ≤ 1 := by
  norm_num [quarterWeights, Fin.sum_univ_two]

private noncomputable def outcomePre (i : Fin 2) :
    SourceAssertion (Fin 2 × ℕ) MeasureLoop.D :=
  selectedIdentity.measureSelectedPreSource (fun _ => MeasureLoop.rq false)
    (fun _ => MeasureLoop.meas false) SourceVariable.fst.set
    (fun _ j => decide (j = i))

private theorem outcomeDeriv (i : Fin 2) :
    SourceDerivTot ((outcomePre i).withClassical (fun _ => True))
      (.measure 2 1 (fun _ => MeasureLoop.rq false)
        (fun _ => MeasureLoop.meas false) SourceVariable.fst.set)
      (selectedIdentity.withClassical (fun σ => σ.1 = i)) := by
  apply SourceDerivTot.conseq _
    (SourceDerivTot.measureSelected (fun _ => MeasureLoop.rq false)
      (fun _ => MeasureLoop.meas false) SourceVariable.fst
      (fun _ j => decide (j = i)) selectedIdentity (fun _ _ => rfl) (fun _ _ _ _ => trivial)) _
  · refine ⟨?_, fun _ _ => ⟨Iff.rfl, fun _ => le_rfl⟩⟩
    intro σ _ j _
    trivial
  · refine ⟨?_, fun _ _ => ⟨Iff.rfl, fun _ => le_rfl⟩⟩
    intro σ h
    change σ.1 = i
    exact of_decide_eq_true h.2

/-- Convex1 combines two actual single-outcome measurement derivations with
weights summing to one half, retaining their exclusive result conditions. -/
theorem convex1MeasurementDeriv :
    SourceDerivTot (SourceAssertion.convex (fun _ => True) outcomePre
        quarterWeights quarterWeights_sum)
      (.measure 2 1 (fun _ => MeasureLoop.rq false)
        (fun _ => MeasureLoop.meas false) SourceVariable.fst.set)
      (SourceAssertion.scaled (fun σ => ∃ i : Fin 2, σ.1 = i) selectedIdentity
        (SourceAssertion.convexMax quarterWeights)
        (SourceAssertion.convexMax_le_one quarterWeights quarterWeights_sum)) := by
  apply SourceDerivTot.convex1 _ _ _ _ _ _ _ _ outcomeDeriv
  intro σ i j hij hi hj
  exact hij (hi.symm.trans hj)

/-- Convex2 accepts a strict subprobability mixture of identity assertions. -/
theorem convex2SubprobDeriv :
    SourceDerivTot
      (SourceAssertion.convex (fun _ => True) (fun _ : Fin 2 => selectedIdentity)
        quarterWeights quarterWeights_sum) .skip
      (SourceAssertion.convex (fun _ => True) (fun _ : Fin 2 => selectedIdentity)
        quarterWeights quarterWeights_sum) :=
  .convex2 _ _ _ _ _ _ _ (fun _ _ _ => trivial) (fun _ => .skip _)

/-- This test's combined quantum predicate is a nonzero one-half identity. -/
theorem convex2Subprob_op (σ : Fin 2 × ℕ) :
    (SourceAssertion.convex (fun _ => True) (fun _ : Fin 2 => selectedIdentity)
      quarterWeights quarterWeights_sum).quantum.op σ = (1 / 2 : ℂ) • 1 := by
  change (∑ i : Fin 2, (quarterWeights i : ℂ) •
    (1 : EndM MeasureLoop.D Finset.univ)) = _
  rw [Fin.sum_univ_two, ← add_smul]
  norm_num [quarterWeights]

#print axioms convex1MeasurementDeriv
#print axioms convex2SubprobDeriv

#print axioms selectedAllDeriv
#print axioms selectedAll_identity_op
#print axioms selectedAttemptDeriv
#print axioms selectedAttemptValid

#print axioms measuredDeriv
#print axioms measuredProgram_eq_mapStore
#print axioms measuredValid
#print axioms countLoopDeriv
#print axioms countLoopValid
#print axioms countedProgramDeriv
#print axioms countedProgramValid

end Qhl.SourceRuleIntegration
