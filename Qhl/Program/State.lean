import Qhl.Program.Syntax
import Qhl.SuperOp.LiftSO

/-!
# P-2: states and configurations

Subgoal P-2 of spec 06 (paper §3.4.2; master `Context.lean:78`,
`DensityCarrier.lean:98`).

Decision W6: quantum states use positive operators on the whole world
`EndM D univ`. The carrier does not impose a trace bound; `IsSubnormal`
selects the partial density operators of trace at most one. Local
operators reach the global space through `liftF`/`liftSO`, exactly as CoqQ
works with `'SO_setT` (`qwhile.v:154`), which removes the threaded world
parameter of master's `CQState Γ W` and all its cast noise.

A configuration is a control (a program still to run, or `done`) together with
a cq-state (a classical state and a positive operator).
-/

namespace Qhl

open Finset
open scoped ComplexOrder NNReal

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {σT : Type*}

/-- P-2: a positive operator on the whole world; `IsSubnormal` supplies the trace bound. -/
structure PDensity {L : Type*} [Fintype L] [DecidableEq L] (D : L → Type*)
    [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] where
  /-- The underlying operator. -/
  op : EndM D (univ : Finset L)
  /-- Density operators are positive. -/
  pos : op.IsPositive

namespace PDensity

@[ext]
theorem ext {ρ ρ' : PDensity D} (h : ρ.op = ρ'.op) : ρ = ρ' := by
  cases ρ; cases ρ'; simpa using h

omit [∀ i, DecidableEq (D i)] in
/-- The trace of a positive operator is a nonnegative real. -/
theorem trace_re_nonneg {x : EndM D (univ : Finset L)} (hx : x.IsPositive) :
    0 ≤ (LinearMap.trace ℂ (HS D (univ : Finset L)) x).re := by
  simpa using (Complex.le_def.mp hx.trace_nonneg).1

/-- The mass (trace) of a partial density operator. -/
noncomputable def mass (ρ : PDensity D) : ℝ≥0 :=
  ⟨(LinearMap.trace ℂ (HS D (univ : Finset L)) ρ.op).re, trace_re_nonneg ρ.pos⟩

@[simp]
theorem coe_mass (ρ : PDensity D) :
    (ρ.mass : ℝ) = (LinearMap.trace ℂ (HS D (univ : Finset L)) ρ.op).re := rfl

/-- Subnormality: the paper's `tr ρ ≤ 1` (§3.4.2). -/
def IsSubnormal (ρ : PDensity D) : Prop := ρ.mass ≤ 1

/-- The zero state (the state of an aborted branch). -/
noncomputable def zero : PDensity D := ⟨0, LinearMap.isPositive_zero⟩

@[simp]
theorem zero_op : (zero : PDensity D).op = 0 := rfl

/-- Conjugation by an operator, `ρ ↦ K ρ K†` — the effect of a unitary or of
one measurement branch. -/
noncomputable def conj (K : EndM D (univ : Finset L)) (ρ : PDensity D) : PDensity D :=
  ⟨K ∘ₗ ρ.op ∘ₗ LinearMap.adjoint K, ρ.pos.conj_adjoint K⟩

@[simp]
theorem conj_op (K : EndM D (univ : Finset L)) (ρ : PDensity D) :
    (conj K ρ).op = K ∘ₗ ρ.op ∘ₗ LinearMap.adjoint K := rfl

/-- The image of a state under a completely positive map — the effect of the
initialisation channel. -/
noncomputable def mapSO (E : SuperOp D (univ : Finset L) (univ : Finset L))
    (hE : IsCP D E) (ρ : PDensity D) : PDensity D :=
  ⟨E ρ.op, IsCP.isPositive_map D hE ρ.pos⟩

@[simp]
theorem mapSO_op (E : SuperOp D (univ : Finset L) (univ : Finset L)) (hE : IsCP D E)
    (ρ : PDensity D) : (mapSO E hE ρ).op = E ρ.op := rfl

end PDensity

/-- P-2: a cq-state — a classical state paired with a partial density
operator (paper §3.4.2). -/
structure CQState (σT : Type*) {L : Type*} [Fintype L] [DecidableEq L]
    (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] where
  /-- The classical state. -/
  cls : σT
  /-- The quantum state. -/
  q : PDensity D

/-- P-2: the control component of a configuration. -/
inductive Control (σT : Type*) {L : Type*} (D : L → Type*)
    [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] : Type _ where
  /-- There is still a program to run. -/
  | running (P : Prog σT D)
  /-- The program has terminated. -/
  | done

/-- P-2: a configuration of the step semantics. -/
structure Config (σT : Type*) {L : Type*} [Fintype L] [DecidableEq L]
    (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] where
  /-- What remains to be run. -/
  ctrl : Control σT D
  /-- The classical state. -/
  cls : σT
  /-- The quantum state. -/
  q : PDensity D

namespace Config

/-- The cq-state of a configuration. -/
def st (c : Config σT D) : CQState σT D := ⟨c.cls, c.q⟩

/-- The mass of a configuration. -/
noncomputable def mass (c : Config σT D) : ℝ≥0 := c.q.mass

/-- A configuration is terminal when nothing remains to be run. -/
def isDone (c : Config σT D) : Bool :=
  match c.ctrl with
  | .done => true
  | .running _ => false

/-- The initial configuration of a program on a cq-state. -/
def init (P : Prog σT D) (s : CQState σT D) : Config σT D := ⟨.running P, s.cls, s.q⟩

/-- The terminal configuration on a cq-state. -/
def term (s : CQState σT D) : Config σT D := ⟨.done, s.cls, s.q⟩

@[simp] theorem isDone_term (s : CQState σT D) : (term s).isDone = true := rfl

@[simp] theorem isDone_init (P : Prog σT D) (s : CQState σT D) :
    (init P s).isDone = false := rfl

end Config

end Qhl
