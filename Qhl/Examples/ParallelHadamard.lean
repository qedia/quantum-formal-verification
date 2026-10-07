import Mathlib.LinearAlgebra.Matrix.Kronecker
import Qhl.Gate.Qubit
import Qhl.History.Correctness

/-!
# E-3: a parallel Hadamard on a parametric quantum array

Subgoal E-3 of spec 06 §7 — the paper's raison d'être for arrays
(arXiv:2412.09869 §2.2, Def 2.1; CoqQ `example.v:51`).

The world is `L = Fin 4`, every cell a qubit, and the classical state
`σT = Fin 4` is used as a *subscript*: the program applies `H ⊗ H` to the pair
of array cells `a[σ], a[σ+1]`. Its register is therefore a genuine register
*expression* (Decision W3) whose two cells move with the classical state, and
the paper's distinctness formula `Dist(q̄)` (eq (2)) has to be discharged
before the step can fire.

The point of the example is that the discharge is **automation**:
`RegExpr.dist_of_array` reduces the two-cell condition to injectivity of the
two subscripts, which `decide` settles over the finite index type — no manual
reasoning about the cell list.

What is proved:

* `distA` — the `Dist` side condition, by `dist_of_array` + `decide`;
* `front_one`, `length_front_one` — the frontier of the run is a *singleton*,
  i.e. the malformed-register clause (paper Prop 3.1(4)) does not fire;
* `termMass_eq`, `terminatingTraceMass_eq` — the step preserves mass.
-/

namespace Qhl.ParallelHadamard

open Finset
open scoped NNReal ENNReal Kronecker

/-! ## The fixture: four qubit cells, the classical state as a subscript -/

/-- The world of the example: four cells. -/
abbrev L : Type := Fin 4

/-- Every cell of the world is a qubit. -/
abbrev D : L → Type := fun _ => Bool

/-- The parametric quantum array indexing all four cells (paper Def 2.1). -/
def arr : QArr (Fin 4) L := Function.Embedding.refl _

/-- The two subscript expressions `σ` and `σ + 1` (W2: shallow classical
expressions). -/
def subs : Fin 2 → Fin 4 → Fin 4 := ![fun σ => σ, fun σ => σ + 1]

/-- The two-cell register expression `a[σ], a[σ+1]`. -/
def regA : RegExpr (Fin 4) L 2 := RegExpr.ofFns fun i => arr.at (subs i)

/-- In the classical state `σ` the register expression names the array cells
`a[σ]` and `a[σ+1]`. -/
theorem regA_apply (σ : Fin 4) : regA σ 0 = σ ∧ regA σ 1 = σ + 1 := ⟨rfl, rfl⟩

/-- E-3: the paper's `Dist(q̄)` (eq (2)) for `a[σ], a[σ+1]`, discharged by
`RegExpr.dist_of_array` — injectivity of the array plus a `decide` on the
subscripts. -/
theorem distA (σ : Fin 4) : RegExpr.dist regA σ :=
  RegExpr.dist_of_array arr subs σ (by revert σ; decide)

/-! ## The gate: `H ⊗ H` on the two-cell tuple space -/

/-- The tensor product of two one-qubit gates, as a gate on `Bool × Bool`
(a local helper: the gate library G-3 ships only the entangling two-qubit
gates and `control`). -/
noncomputable def kronOp (U V : UnitaryOp 𝕢) : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)) :=
  unitaryOfMat (unitaryMat U ⊗ₖ unitaryMat V) <| by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      unitaryMat_conjTranspose_mul, unitaryMat_conjTranspose_mul,
      Matrix.one_kronecker_one]

/-- The parallel Hadamard `H ⊗ H`, moved onto the tuple space of the two-cell
register expression (R-2: reindexing along `Fin 2 → Bool ≃ Bool × Bool`). -/
noncomputable def gateHH (σ : Fin 4) : UnitaryOp (TSpace D (regA σ)) :=
  euclCongrOp (piFinTwoEquiv fun _ => Bool).symm (kronOp H H)

/-- E-3: the program `a[σ], a[σ+1] *= H ⊗ H`. -/
noncomputable def parProg : Prog (Fin 4) D := .unitary 2 regA gateHH

/-! ## The run -/

/-- The state after the parallel Hadamard. -/
noncomputable def afterHH (s : CQState (Fin 4) D) : PDensity D :=
  s.q.conj (regLift ⟨regA s.cls, distA s.cls⟩ (gateHH s.cls))

/-- E-3: the step fires — the frontier at depth one is a singleton, so the
malformed-register clause (paper Prop 3.1(4)) is not taken. -/
theorem front_one (s : CQState (Fin 4) D) :
    boundedFront (Config.init parProg s) 1 = [Config.term ⟨s.cls, afterHH s⟩] := by
  rw [parProg, boundedFront_unitary regA gateHH s (distA s.cls)]
  rfl

/-- E-3, branch count form: exactly one successor. -/
theorem length_front_one (s : CQState (Fin 4) D) :
    (boundedFront (Config.init parProg s) 1).length = 1 := by
  rw [front_one]
  rfl

/-- The gate is unitary, so the step preserves mass. -/
theorem mass_afterHH (s : CQState (Fin 4) D) : (afterHH s).mass = s.q.mass :=
  PDensity.mass_conj_of_isUnitary
    (isUnitary_regLift ⟨regA s.cls, distA s.cls⟩ (gateHH s.cls)) s.q

/-- From depth two on nothing is left to run. -/
theorem front_add_two (s : CQState (Fin 4) D) (n : ℕ) :
    boundedFront (Config.init parProg s) (n + 2) = [] := by
  induction n with
  | zero => rw [show (0 : ℕ) + 2 = 1 + 1 from rfl, boundedFront_succ, front_one]; rfl
  | succ n ih => rw [show n + 1 + 2 = (n + 2) + 1 from rfl, boundedFront_succ, ih]; rfl

/-- E-3: all the mass terminates at depth exactly one. -/
theorem termMass_eq (s : CQState (Fin 4) D) (n : ℕ) :
    termMass (Config.init parProg s) n = if n = 1 then s.q.mass else 0 := by
  match n with
  | 0 => rw [termMass]; rfl
  | 1 =>
      rw [termMass, front_one, if_pos rfl]
      simp only [List.filter_cons, Config.isDone_term, if_true, List.filter_nil,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact mass_afterHH s
  | (n + 2) => rw [termMass, front_add_two]; rfl

/-- E-3: the program preserves mass (paper eq (7)). -/
theorem terminatingTraceMass_eq (s : CQState (Fin 4) D) :
    terminatingTraceMass (Config.init parProg s) = (s.q.mass : ℝ≥0∞) := by
  rw [terminatingTraceMass,
    tsum_eq_single 1 fun n hn => by rw [termMass_eq s n, if_neg hn]; rfl]
  rw [termMass_eq s 1, if_pos rfl]

end Qhl.ParallelHadamard
