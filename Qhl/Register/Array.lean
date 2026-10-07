import Qhl.Register.Basic

/-!
# R-5: parametric quantum arrays and register expressions

Subgoal R-5 of spec 06 (Decision W3). A *parametric quantum array* of the
paper (Def 2.1, arXiv:2412.09869 §2.2) is an injective map from a classical
index type into the world of cells, `QArr ι L := ι ↪ L`; the subscripted
variable `a[s̄]` is the function `fun σ => a (s σ)`.

A *register expression* is a σ-indexed tuple of cells, `RegExpr σT L k :=
σT → Fin k → L`. The paper's distinctness side condition `Dist(q̄)` (eq (2))
is `RegExpr.dist`, which is decidable; the step semantics evaluates a
register expression with `RegExpr.eval?` and produces *no* transition when it
fails (paper Prop 3.1(4,5); master `evalQArray? = none ⇒ []`).
-/

namespace Qhl

variable {L σT ι : Type*} {k : ℕ}

/-- A parametric quantum array: an injective indexing of cells by a classical
index type (paper Def 2.1). -/
abbrev QArr (ι L : Type*) : Type _ := ι ↪ L

/-- A register expression: a classical-state-dependent tuple of `k` cells. -/
abbrev RegExpr (σT L : Type*) (k : ℕ) : Type _ := σT → Fin k → L

/-- The subscripted array variable `a[s]` of paper Def 2.1: a cell expression. -/
def QArr.at (a : QArr ι L) (s : σT → ι) : σT → L := fun σ => a (s σ)

@[simp]
theorem QArr.at_apply (a : QArr ι L) (s : σT → ι) (σ : σT) : a.at s σ = a (s σ) := rfl

namespace RegExpr

/-- Assemble a register expression from `k` cell expressions. -/
def ofFns (f : Fin k → σT → L) : RegExpr σT L k := fun σ i => f i σ

@[simp]
theorem ofFns_apply (f : Fin k → σT → L) (σ : σT) (i : Fin k) : ofFns f σ i = f i σ := rfl

/-- A register expression that does not depend on the classical state. -/
def const [DecidableEq L] (r : Reg L k) : RegExpr σT L k := fun _ => r.toFun

variable [DecidableEq L]

/-- The paper's distinctness formula `Dist(q̄)` (eq (2)): the cells named by
the register expression are pairwise distinct in the classical state `σ`. -/
def dist (r : RegExpr σT L k) (σ : σT) : Prop := Function.Injective (r σ)

instance (r : RegExpr σT L k) (σ : σT) : Decidable (r.dist σ) :=
  inferInstanceAs (Decidable (Function.Injective (r σ)))

@[simp]
theorem dist_const (r : Reg L k) (σ : σT) : dist (const (σT := σT) r) σ := r.inj

/-- Evaluation of a register expression: a register when the cells are
distinct, `none` otherwise (master `evalQArray?`). -/
def eval? (r : RegExpr σT L k) (σ : σT) : Option (Reg L k) :=
  if h : r.dist σ then some ⟨r σ, h⟩ else none

@[simp]
theorem eval?_eq_some (r : RegExpr σT L k) (σ : σT) (h : r.dist σ) :
    r.eval? σ = some ⟨r σ, h⟩ := dif_pos h

@[simp]
theorem eval?_eq_none (r : RegExpr σT L k) (σ : σT) (h : ¬ r.dist σ) :
    r.eval? σ = none := dif_neg h

theorem eval?_isSome_iff (r : RegExpr σT L k) (σ : σT) :
    (r.eval? σ).isSome ↔ r.dist σ := by
  by_cases h : r.dist σ <;> simp [eval?, h]

omit [DecidableEq L] in
/-- E-3's side condition: a tuple of subscripts of one array is distinct as
soon as the subscripts themselves are, since the array is injective. -/
theorem dist_of_array (a : QArr ι L) (s : Fin k → σT → ι) (σ : σT)
    (h : Function.Injective fun i => s i σ) :
    dist (ofFns fun i => a.at (s i)) σ := by
  intro i j hij
  exact h (a.injective hij)

end RegExpr

end Qhl
