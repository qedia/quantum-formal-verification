import Qhl.History.Denotation

/-!
# T-5: correctness formulas

Subgoal T-5 of spec 06 (paper Def 5.1; master
`HistoryCorrectnessFormula.lean:30-72`).

A cq-assertion is a classical predicate together with a state-indexed effect
(`0 ≤ A σ ≤ 1`); the Dirac layer of spec 03 supplies concrete effects through
`Reg.linD`/`liftF` in the examples. The two judgements are the usual
inequality forms:

* total correctness `⊨tot`: the initial expectation is dominated by the
  expectation accumulated over *terminated* histories;
* partial correctness `⊨par`: the same, allowing the nontermination quantity
  `NT` (paper eq (8)) as slack.

The QHL⁺ *proof system* (paper §5) is deliberately out of scope: the point of
this file is that triples are **statable** against a fixed concrete semantics,
so rules can be added later without touching the model.
-/

namespace Qhl

open Finset
open scoped NNReal ENNReal ComplexOrder

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-- T-5: a cq-assertion (paper Def 5.1): a classical predicate together with a
family of effects on the global space. -/
structure CQAssertion (σT : Type*) {L : Type*} [Fintype L] [DecidableEq L]
    (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] where
  /-- The classical component. -/
  cls : σT → Prop
  /-- The quantum component. -/
  op : σT → EndM D (univ : Finset L)
  /-- The quantum component is an effect, `0 ≤ op σ ≤ 1`. -/
  isEffect : ∀ σ, IsEffect (op σ)

/-- The expectation of an effect in a cq-state, `Tr (ρ A)`. -/
noncomputable def expect (A : σT → EndM D (univ : Finset L)) (s : CQState σT D) : ℝ :=
  (LinearMap.trace ℂ (HS D (univ : Finset L)) (s.q.op ∘ₗ A s.cls)).re

omit [∀ i, Inhabited (D i)] in
theorem expect_nonneg {A : σT → EndM D (univ : Finset L)}
    (hA : ∀ σ, (A σ).IsPositive) (s : CQState σT D) : 0 ≤ expect A s := by
  rw [expect]
  simpa using (Complex.le_def.mp (trace_comp_nonneg s.q.pos (hA s.cls))).1

omit [∀ i, Inhabited (D i)] in
theorem expect_le_mass {A : σT → EndM D (univ : Finset L)}
    (hA : ∀ σ, IsEffect (A σ)) (s : CQState σT D) : expect A s ≤ s.q.mass := by
  have h := trace_comp_mono s.q.pos (hA s.cls).2
  rw [Module.End.one_eq_id, LinearMap.comp_id] at h
  simpa [expect] using (Complex.le_def.mp h).1

/-! ## The post-expectation of a program run -/

/-- The expectation accumulated by the histories terminating at depth `n`. -/
noncomputable def postAt (root : Config σT D) (n : ℕ)
    (A : σT → EndM D (univ : Finset L)) : ℝ :=
  (((boundedFront root n).filter fun c => c.isDone).map fun c => expect A c.st).sum

theorem postAt_nonneg {A : σT → EndM D (univ : Finset L)}
    (hA : ∀ σ, (A σ).IsPositive) (root : Config σT D) (n : ℕ) :
    0 ≤ postAt root n A := by
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
  exact expect_nonneg hA c.st

/-- The post-expectation of an effect never exceeds the terminating mass. -/
theorem postAt_le_termMass {A : σT → EndM D (univ : Finset L)}
    (hA : ∀ σ, IsEffect (A σ)) (root : Config σT D) (n : ℕ) :
    postAt root n A ≤ (termMass root n : ℝ) := by
  rw [postAt, termMass, NNReal.coe_list_sum, List.map_map]
  refine List.sum_le_sum fun c _ => ?_
  exact expect_le_mass hA c.st

/-- T-5: the total post-expectation of a run (the `PostH` of master). -/
noncomputable def PostH (root : Config σT D) (A : σT → EndM D (univ : Finset L)) :
    ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (postAt root n A)

/-- T-5: the terminating mass of a run (the `TermH` of master). -/
noncomputable def TermH (root : Config σT D) : ℝ≥0∞ := terminatingTraceMass root

/-- T-5: the nontermination quantity of a run (the `NTH` of master, paper
eq (8)). -/
noncomputable def NTH (root : Config σT D) : ℝ≥0∞ := NT root

theorem PostH_le_TermH {A : σT → EndM D (univ : Finset L)} (hA : ∀ σ, IsEffect (A σ))
    (root : Config σT D) : PostH root A ≤ TermH root := by
  refine ENNReal.tsum_le_tsum fun n => ?_
  calc ENNReal.ofReal (postAt root n A)
      ≤ ENNReal.ofReal ((termMass root n : ℝ)) :=
        ENNReal.ofReal_le_ofReal (postAt_le_termMass hA root n)
    _ = (termMass root n : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

theorem PostH_le_mass {A : σT → EndM D (univ : Finset L)} (hA : ∀ σ, IsEffect (A σ))
    (root : Config σT D) : PostH root A ≤ (root.mass : ℝ≥0∞) :=
  le_trans (PostH_le_TermH hA root) (terminatingTraceMass_le root)

theorem TermH_add_NTH (root : Config σT D) : TermH root + NTH root = (root.mass : ℝ≥0∞) :=
  terminatingTraceMass_add_NT root

/-! ## T-5: the two correctness judgements (paper Def 5.1, (19)/(20)) -/

/-- Total correctness: the initial expectation is dominated by the
post-expectation over terminated histories. -/
def modelsTotH (q : CQAssertion σT D) (P : Prog σT D) (q' : CQAssertion σT D) : Prop :=
  ∀ s : CQState σT D, q.cls s.cls →
    ENNReal.ofReal (expect q.op s) ≤ PostH (Config.init P s) q'.op

/-- Partial correctness: total correctness with the nontermination quantity as
slack. -/
def modelsParH (q : CQAssertion σT D) (P : Prog σT D) (q' : CQAssertion σT D) : Prop :=
  ∀ s : CQState σT D, q.cls s.cls →
    ENNReal.ofReal (expect q.op s)
      ≤ PostH (Config.init P s) q'.op + NTH (Config.init P s)

/-- M9 acceptance: total correctness implies partial correctness. -/
theorem modelsTotH.modelsParH {q q' : CQAssertion σT D} {P : Prog σT D}
    (h : modelsTotH q P q') : modelsParH q P q' := fun s hs =>
  le_trans (h s hs) le_self_add

end Qhl
