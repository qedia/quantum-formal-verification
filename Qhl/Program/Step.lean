import Qhl.Program.State
import Qhl.Gate.Init

/-!
# P-3: the step semantics of qWhile⁺

Subgoal P-3 of spec 06 (paper Table 2; master `DirectStep.lean:144`).

`next : Config → List Config` is list-valued: one entry per transition
sanctioned by Table 2, in a fixed order, with *unnormalised* quantum states
(the branch probability is carried by the mass, paper §3.4.2). The list is
empty for a terminated configuration and — Decision W3 — also for a
malformed register expression, which is exactly the paper's Prop 3.1(4,5)
(master: `evalQArray? = none ⇒ []`).

The recursion is structural in the program: only the `seq` clause recurses,
on its first component.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-- The global-space operator of a gate applied to an evaluated register:
transport along `Reg.encode` (R-3), then cylindrical extension to the whole
world (W6). -/
noncomputable def regLift {k : ℕ} (r : Reg L k)
    (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) : EndM D (univ : Finset L) :=
  liftF D (subset_univ r.sig) (r.op D A)

/-- W6, entry form: the cylindrical extension of a register gate is the gate's
matrix on the register's cells, times a Kronecker delta on the rest of the
world. -/
theorem regLift_deltav_apply {k : ℕ} (r : Reg L k)
    (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) (m l : QIdx D (univ : Finset L)) :
    regLift r A (deltav D m) l
      = r.op D A (deltav D (QIdx.res D (subset_univ r.sig) m))
          (QIdx.res D (subset_univ r.sig) l)
        * (if QIdx.res D (sdiff_subset : (univ : Finset L) \ r.sig ⊆ univ) l
            = QIdx.res D (sdiff_subset : (univ : Finset L) \ r.sig ⊆ univ) m then 1 else 0) :=
  liftF_deltav_apply D (subset_univ r.sig) (r.op D A) m l

/-- The initialisation channel of a cell set, extended to the whole world. -/
noncomputable def initLift (S : Finset L) :
    SuperOp D (univ : Finset L) (univ : Finset L) :=
  liftSO D (subset_univ S) (initSO D S)

theorem initLift_isQC (S : Finset L) : IsQC D (initLift (D := D) S) :=
  IsQC.liftSO D (subset_univ S) (initSO_isQC D)

namespace Control

/-- Sequencing on controls: what remains after one step of `P₁` inside
`P₁; P₂`. -/
def seqWith (c : Control σT D) (P₂ : Prog σT D) : Control σT D :=
  match c with
  | .running P₁ => .running (.seq P₁ P₂)
  | .done => .running P₂

@[simp]
theorem seqWith_running (P₁ P₂ : Prog σT D) :
    (Control.running P₁).seqWith P₂ = .running (.seq P₁ P₂) := rfl

@[simp]
theorem seqWith_done (P₂ : Prog σT D) : (Control.done (σT := σT)).seqWith P₂
    = .running P₂ := rfl

end Control

/-- P-3: one step of a program on a cq-state, as the list of successor
configurations (paper Table 2). -/
noncomputable def stepProg : Prog σT D → σT → PDensity D → List (Config σT D)
  | .skip, σ, ρ => [⟨.done, σ, ρ⟩]
  | .assign f, σ, ρ => [⟨.done, f σ, ρ⟩]
  | .init S, σ, ρ =>
      [⟨.done, σ, ρ.mapSO (initLift (S σ)) (initLift_isQC (S σ)).1⟩]
  | .unitary _ r U, σ, ρ =>
      if h : Function.Injective (r σ) then
        [⟨.done, σ, ρ.conj (regLift ⟨r σ, h⟩ (U σ))⟩]
      else []
  | .measure m _ r M upd, σ, ρ =>
      if h : Function.Injective (r σ) then
        (List.finRange m).map fun i =>
          ⟨.done, upd i σ, ρ.conj (regLift ⟨r σ, h⟩ ((M σ).M i))⟩
      else []
  | .seq P₁ P₂, σ, ρ =>
      (stepProg P₁ σ ρ).map fun c => ⟨c.ctrl.seqWith P₂, c.cls, c.q⟩
  | .ite b P₁ P₀, σ, ρ =>
      [⟨.running (if b σ then P₁ else P₀), σ, ρ⟩]
  | .while b P, σ, ρ =>
      if b σ then [⟨.running (.seq P (.while b P)), σ, ρ⟩] else [⟨.done, σ, ρ⟩]

/-- P-3: one step of a configuration; a terminated configuration has no
successor. -/
noncomputable def next (c : Config σT D) : List (Config σT D) :=
  match c.ctrl with
  | .done => []
  | .running P => stepProg P c.cls c.q

/-- The one-step transition relation. -/
def Step (c c' : Config σT D) : Prop := c' ∈ next c

/-! ## Clause-by-clause description of `next` (master's `Spec/` discipline) -/

@[simp]
theorem next_done (σ : σT) (ρ : PDensity D) :
    next (⟨.done, σ, ρ⟩ : Config σT D) = [] := rfl

@[simp]
theorem next_running (P : Prog σT D) (σ : σT) (ρ : PDensity D) :
    next (⟨.running P, σ, ρ⟩ : Config σT D) = stepProg P σ ρ := rfl

@[simp]
theorem stepProg_skip (σ : σT) (ρ : PDensity D) :
    stepProg (.skip : Prog σT D) σ ρ = [⟨.done, σ, ρ⟩] := rfl

@[simp]
theorem stepProg_assign (f : σT → σT) (σ : σT) (ρ : PDensity D) :
    stepProg (.assign f : Prog σT D) σ ρ = [⟨.done, f σ, ρ⟩] := rfl

@[simp]
theorem stepProg_init (S : σT → Finset L) (σ : σT) (ρ : PDensity D) :
    stepProg (.init S : Prog σT D) σ ρ =
      [⟨.done, σ, ρ.mapSO (initLift (S σ)) (initLift_isQC (S σ)).1⟩] := rfl

theorem stepProg_unitary {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (σ : σT) (ρ : PDensity D)
    (h : Function.Injective (r σ)) :
    stepProg (.unitary k r U) σ ρ = [⟨.done, σ, ρ.conj (regLift ⟨r σ, h⟩ (U σ))⟩] :=
  dif_pos h

/-- W3: a malformed register expression yields no transition (paper
Prop 3.1(4)). -/
theorem stepProg_unitary_of_not_dist {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (σ : σT) (ρ : PDensity D)
    (h : ¬ Function.Injective (r σ)) :
    stepProg (.unitary k r U) σ ρ = [] :=
  dif_neg h

theorem stepProg_measure {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ))) (upd : Fin m → σT → σT) (σ : σT)
    (ρ : PDensity D) (h : Function.Injective (r σ)) :
    stepProg (.measure m k r M upd) σ ρ =
      (List.finRange m).map fun i =>
        ⟨.done, upd i σ, ρ.conj (regLift ⟨r σ, h⟩ ((M σ).M i))⟩ :=
  dif_pos h

/-- W3: a malformed register expression yields no transition (paper
Prop 3.1(5)). -/
theorem stepProg_measure_of_not_dist {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ))) (upd : Fin m → σT → σT) (σ : σT)
    (ρ : PDensity D) (h : ¬ Function.Injective (r σ)) :
    stepProg (.measure m k r M upd) σ ρ = [] :=
  dif_neg h

@[simp]
theorem stepProg_seq (P₁ P₂ : Prog σT D) (σ : σT) (ρ : PDensity D) :
    stepProg (.seq P₁ P₂) σ ρ =
      (stepProg P₁ σ ρ).map fun c => ⟨c.ctrl.seqWith P₂, c.cls, c.q⟩ := rfl

@[simp]
theorem stepProg_ite (b : σT → Bool) (P₁ P₀ : Prog σT D) (σ : σT) (ρ : PDensity D) :
    stepProg (.ite b P₁ P₀) σ ρ = [⟨.running (if b σ then P₁ else P₀), σ, ρ⟩] := rfl

theorem stepProg_while_true (b : σT → Bool) (P : Prog σT D) (σ : σT) (ρ : PDensity D)
    (h : b σ = true) :
    stepProg (.while b P) σ ρ = [⟨.running (.seq P (.while b P)), σ, ρ⟩] := by
  simp [stepProg, h]

theorem stepProg_while_false (b : σT → Bool) (P : Prog σT D) (σ : σT) (ρ : PDensity D)
    (h : b σ = false) :
    stepProg (.while b P) σ ρ = [⟨.done, σ, ρ⟩] := by
  simp [stepProg, h]

end Qhl
