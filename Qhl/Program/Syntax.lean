import Qhl.Register.Array
import Qhl.Gate.Measure

/-!
# P-1: the syntax of qWhile⁺

Subgoal P-1 of spec 06 (paper Def 3.1, eq (3); master `Syntax.lean:16`).

The four design decisions visible here:

* **W1/W5** — gates and measurements are *concrete bundled objects* carried by
  the constructors (`UnitaryOp`, `QMeasure`), so there is no context record and
  no lawfulness hypothesis anywhere downstream (CoqQ `qwhile.v:124`).
* **W2** — the classical layer is shallow: assignments are `σT → σT`, guards
  are `σT → Bool`, outcome write-backs are `Fin m → σT → σT`.
* **W3** — quantum variables are *register expressions* `σT → Fin k → L`
  (spec 06 R-5); the distinctness condition `Dist(q̄)` is **not** part of the
  syntax, it is checked by the semantics (P-3).
* **W8** — measurement outcomes are `Fin m`; any other finite outcome type is
  absorbed into the write-back function through an equivalence.

The σ-dependence of `U`/`M` is the paper's parameterised gate `U(t̄)` (§3.1)
*and* the σ-dependence of the register's cell types; for a constant register
expression it degenerates to a constant family.
-/

namespace Qhl

/-- P-1: qWhile⁺ programs over the classical state type `σT` and the world of
cells `(L, D)`. Paper Def 3.1 (eq (3)). -/
inductive Prog (σT : Type*) {L : Type*} (D : L → Type*)
    [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] : Type _ where
  /-- `skip`. -/
  | skip
  /-- Classical assignment `x := e`, shallow (W2). -/
  | assign (f : σT → σT)
  /-- Initialisation `q̄ := ∣0…0⟩` of a classical-state-dependent cell set. -/
  | init (S : σT → Finset L)
  /-- Unitary application `q̄ *= U`, with the gate bundled (W5). -/
  | unitary (k : ℕ) (r : RegExpr σT L k) (U : ∀ σ, UnitaryOp (TSpace D (r σ)))
  /-- Measurement `x := M[q̄]`, with the measurement bundled (W5) and the
  outcome written back classically (W2/W8). -/
  | measure (m k : ℕ) (r : RegExpr σT L k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
      (upd : Fin m → σT → σT)
  /-- Sequential composition. -/
  | seq (P₁ P₂ : Prog σT D)
  /-- Classical conditional. -/
  | ite (b : σT → Bool) (P₁ P₀ : Prog σT D)
  /-- Classical while loop. -/
  | while (b : σT → Bool) (P : Prog σT D)

namespace Prog

variable {σT : Type*} {L : Type*} {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]

/-- The size of a program, for well-founded arguments on the history layer. -/
def size : Prog σT D → ℕ
  | .skip | .assign _ | .init _ | .unitary _ _ _ | .measure _ _ _ _ _ => 1
  | .seq P₁ P₂ => P₁.size + P₂.size + 1
  | .ite _ P₁ P₀ => P₁.size + P₀.size + 1
  | .while _ P => P.size + 1

/-- Applying a single-cell gate to the cell named by a classical expression. -/
def unitary1 (c : σT → L) (U : ∀ σ, UnitaryOp (TSpace D fun _ : Fin 1 => c σ)) :
    Prog σT D :=
  .unitary 1 (fun σ _ => c σ) U

end Prog

end Qhl
