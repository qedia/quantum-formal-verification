import Qhl.History.Correctness

/-!
# E-2: a measurement loop

Subgoal E-2 of spec 06 §7: the repeat-until-success shaped program

```
while ¬flag do  flag := M[q]  od
```

over a world of a single qubit cell (`L = Unit`) and a one-bit classical
state (`σT = Bool`, the flag). The body is the computational-basis
measurement `basisMeas` of the cell, whose outcome is written back into the
flag by `upd` (Decisions W2/W8); the loop therefore keeps measuring until it
observes `1`.

What is proved:

* `front_one_unfold` / `front_one_exit` — the loop unfolds when the flag is
  `false` and terminates when it is `true` (paper Prop 3.1(8,9));
* `front_body`, `length_front_body` — one execution of the body has exactly
  two branches, one per measurement outcome;
* `branch_mass_add` — the two branch masses sum to the incoming mass
  (`stepMass_measure`, i.e. the completeness relation carried by `QMeasure`);
* `frontMass_le` — no depth of the (possibly nonterminating) run ever carries
  more mass than the initial configuration.
-/

namespace Qhl.MeasureLoop

open Finset
open scoped NNReal

/-! ## The fixture: one qubit cell, a one-bit classical state -/

/-- The world of the example: a single cell. -/
abbrev L : Type := Unit

/-- The cell of the world is a qubit. -/
abbrev D : L → Type := fun _ => Bool

/-- The one-cell register expression naming the only cell. -/
def rq : RegExpr Bool L 1 := RegExpr.const (Reg.single ())

/-- The register expression is well formed in every classical state. -/
theorem distQ (σ : Bool) : Function.Injective (rq σ) := (Reg.single (() : L)).inj

/-! ## The measurement and the loop -/

/-- The outcomes `Fin 2` read as classical bits, through the tuple space of a
one-cell register. -/
def outcomeEquiv : Fin 2 ≃ TIdx D (rq false) :=
  finTwoEquiv.trans (Equiv.funUnique (Fin 1) Bool).symm

/-- The computational-basis measurement of the cell (G-4). -/
noncomputable def meas (σ : Bool) : QMeasure 2 (TSpace D (rq σ)) := basisMeas outcomeEquiv

/-- The write-back: the flag becomes the observed bit (W2/W8). -/
def upd : Fin 2 → Bool → Bool := fun i _ => finTwoEquiv i

/-- The loop guard: keep going while the flag is `false`. -/
def flagFalse : Bool → Bool := fun σ => !σ

/-- The loop body: measure the cell and store the outcome in the flag. -/
noncomputable def body : Prog Bool D := .measure 2 1 rq meas upd

/-- E-2: the measurement loop `while ¬flag do flag := M[q] od`. -/
noncomputable def loopProg : Prog Bool D := .while flagFalse body

/-! ## Unfolding the loop -/

/-- The loop unfolds while the flag is `false` (paper Prop 3.1(8)). -/
theorem front_one_unfold (s : CQState Bool D) (h : s.cls = false) :
    boundedFront (Config.init loopProg s) 1 = [Config.init (.seq body loopProg) s] := by
  rw [loopProg, boundedFront_while_true flagFalse body s (by simp [flagFalse, h])]

/-- The loop terminates once the flag is `true` (paper Prop 3.1(9)). -/
theorem front_one_exit (s : CQState Bool D) (h : s.cls = true) :
    boundedFront (Config.init loopProg s) 1 = [Config.term s] := by
  rw [loopProg, boundedFront_while_false flagFalse body s (by simp [flagFalse, h])]

/-! ## The two branches of the measurement -/

/-- The branch of the body corresponding to the outcome `i`. -/
noncomputable def branch (s : CQState Bool D) (i : Fin 2) : Config Bool D :=
  Config.term ⟨upd i s.cls, s.q.conj (regLift ⟨rq s.cls, distQ s.cls⟩ ((meas s.cls).M i))⟩

/-- One execution of the body produces one configuration per outcome. -/
theorem front_body (s : CQState Bool D) :
    boundedFront (Config.init body s) 1 = [branch s 0, branch s 1] := by
  rw [body, boundedFront_measure rq meas upd s (distQ s.cls)]
  rfl

/-- E-2: the measurement step has exactly two branches. -/
theorem length_front_body (s : CQState Bool D) :
    (boundedFront (Config.init body s) 1).length = 2 := by
  rw [front_body]
  rfl

/-- E-2: the two branch masses sum to the incoming mass — the completeness
relation of the bundled measurement (Decision W5). -/
theorem branch_mass_add (s : CQState Bool D) :
    (branch s 0).mass + (branch s 1).mass = s.q.mass := by
  have h := stepMass_measure rq meas upd s.cls s.q (distQ s.cls)
  rw [stepMass, stepProg_measure rq meas upd s.cls s.q (distQ s.cls),
    show (List.finRange 2) = [0, 1] from rfl] at h
  simpa [branch, Config.mass, Config.term] using h

/-! ## The run never creates mass -/

/-- E-2: at every depth the frontier of the loop carries at most the initial
mass (paper Prop 3.2), even though the loop need not terminate. -/
theorem frontMass_le (s : CQState Bool D) (n : ℕ) :
    frontMass (Config.init loopProg s) n ≤ (Config.init loopProg s).mass := by
  induction n with
  | zero => exact le_of_eq (frontMass_zero _)
  | succ n ih =>
      refine le_trans ?_ ih
      exact le_trans le_add_self (termMass_add_frontMass_succ_le (Config.init loopProg s) n)

end Qhl.MeasureLoop
