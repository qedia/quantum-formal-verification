import Qhl.Logic.Soundness
import Qhl.Examples.MeasureLoop

/-!
# L-7: end-to-end derivations in `QHL⁺`

Subgoal L-7 of spec 07 (milestone M13). Two derivations that exercise the two
loop rules and carry real semantic content through `DerivPar.sound` /
`DerivTot.sound`:

* **partial correctness of the E-2 measurement loop** (`Qhl/Examples/MeasureLoop.lean`,
  `while ¬flag do flag := M[q] od`): `{1} loop {1 ∧ flag}` — *every terminating
  run ends with the flag set*. The loop invariant is `1`; its premise is the
  measurement axiom followed by (R-Conseq), the entailment being exactly the
  completeness relation `Σᵢ Mᵢ†Mᵢ = 1` (`Assn.measurePre_one_op`).
* **total correctness of a classical countdown** `while 0 < x do x := x - 1 od`
  with ranking function `t := id`: `{1} countdown {1 ∧ x = 0}` in
  `QHL⁺_tot`, i.e. *all* the mass terminates.
-/

namespace Qhl.MeasureLoop

open Qhl Finset
open scoped NNReal ENNReal

/-! ## L-7a: partial correctness of the measurement loop -/

/-- The loop invariant `1` entails the measurement precondition: on the `Dist`
branch (which always holds for this constant one-cell register) the
transformer of `1` is `Σᵢ Mᵢ†Mᵢ = 1`. -/
theorem one_mand_le_measurePre :
    (Assn.one : Assn Bool D).mand flagFalse
      ≤ (Assn.one : Assn Bool D).measurePre rq meas upd := by
  intro σ
  rw [Assn.measurePre_one_op rq meas upd (distQ σ)]
  exact (((Assn.one : Assn Bool D).mand flagFalse).isEffect σ).2

/-- The loop body preserves the invariant: the measurement axiom, weakened by
(R-Conseq). -/
theorem bodyDeriv :
    DerivPar ((Assn.one : Assn Bool D).mand flagFalse) body (Assn.one : Assn Bool D) :=
  DerivPar.conseq one_mand_le_measurePre
    (DerivPar.measure rq meas upd Assn.one) (Assn.le_refl' _)

/-- **L-7a**: `{1} while ¬flag do flag := M[q] od {1 ∧ flag}` is derivable in
`QHL⁺_par` — (R-Loop-par) with invariant `1`. -/
theorem loopDeriv :
    DerivPar (Assn.one : Assn Bool D) loopProg
      ((Assn.one : Assn Bool D).mandNot flagFalse) :=
  DerivPar.whileLoop bodyDeriv

/-- The semantic content of `loopDeriv`, through soundness. -/
theorem loopValid :
    validPar (Assn.one : Assn Bool D) loopProg
      ((Assn.one : Assn Bool D).mandNot flagFalse) :=
  loopDeriv.sound

/-- **L-7a, unfolded**: all the initial mass either fails to terminate or
terminates in a state whose flag is set. -/
theorem loop_mass_le (s : CQState Bool D) :
    ((s.q.mass : ℝ≥0) : ℝ≥0∞)
      ≤ PostH (Config.init loopProg s) ((Assn.one : Assn Bool D).mandNot flagFalse).op
        + NT (Config.init loopProg s) := by
  have h := loopValid s
  rwa [expectE_one] at h

end Qhl.MeasureLoop

namespace Qhl.Countdown

open Qhl Finset
open scoped NNReal ENNReal

/-! ## L-7b: total correctness of a classical countdown -/

/-- The world of the example: a single qubit cell (the quantum part is inert
here — the point is the ranking-function loop rule). -/
abbrev L : Type := Unit

/-- The cell of the world is a qubit. -/
abbrev D : L → Type := fun _ => Bool

/-- The loop guard `0 < x`. -/
def guardPos : ℕ → Bool := fun x => decide (0 < x)

/-- The loop body `x := x - 1`. -/
noncomputable def dec : Prog ℕ D := .assign fun x => x - 1

/-- The countdown loop `while 0 < x do x := x - 1 od`. -/
noncomputable def countdown : Prog ℕ D := .while guardPos dec

/-- The ranking function: the counter itself (V3: valued in `ℕ`, so the
paper's side condition `φ → t ≥ 0` is free). -/
def rank : ℕ → ℕ := id

/-- The entailment behind the body's premise: if the guard holds and the
counter is `n`, then after decrementing the counter is below `n`. -/
theorem premise_le (n : ℕ) :
    (((Assn.one : Assn ℕ D).mand guardPos).mask fun σ => rank σ = n)
      ≤ ((Assn.one : Assn ℕ D).mask fun σ => rank σ < n).comp fun x => x - 1 := by
  intro σ
  by_cases hn : rank σ = n
  · by_cases hg : guardPos σ = true
    · -- the guard holds, so the counter is positive and really decreases
      have hlt : rank (σ - 1) < n := by
        simp only [guardPos, decide_eq_true_eq] at hg
        simp only [rank, id] at hn ⊢
        omega
      refine Assn.le_op_of_eq_one ?_
      exact (Assn.mask_op_of_pos (A := (Assn.one : Assn ℕ D))
        (φ := fun σ => rank σ < n) (σ := σ - 1) hlt).trans (Assn.one_op _)
    · -- the guard fails: the precondition's `mand` mask is closed
      refine Assn.op_zero_le ?_
      rw [Assn.mask_op_of_pos (A := (Assn.one : Assn ℕ D).mand guardPos)
        (φ := fun σ => rank σ = n) (σ := σ) hn]
      exact Assn.mand_op_of_false (A := (Assn.one : Assn ℕ D)) (b := guardPos)
        (σ := σ) (by simpa using hg)
  · -- the ranking mask is closed
    refine Assn.op_zero_le ?_
    exact Assn.mask_op_of_neg (A := (Assn.one : Assn ℕ D).mand guardPos)
      (φ := fun σ => rank σ = n) (σ := σ) hn

/-- The body's premise for the ranking value `n`: the assignment axiom,
weakened by (R-Conseq). -/
theorem decDeriv (n : ℕ) :
    DerivTot (((Assn.one : Assn ℕ D).mand guardPos).mask fun σ => rank σ = n) dec
      ((Assn.one : Assn ℕ D).mask fun σ => rank σ < n) :=
  DerivTot.conseq (premise_le n)
    (DerivTot.assign (fun x => x - 1) ((Assn.one : Assn ℕ D).mask fun σ => rank σ < n))
    (Assn.le_refl' _)

/-- **L-7b**: `{1} while 0 < x do x := x - 1 od {1 ∧ x = 0}` is derivable in
`QHL⁺_tot` — (R-Loop-tot) with ranking function `rank`. -/
theorem countdownDeriv :
    DerivTot (Assn.one : Assn ℕ D) countdown
      ((Assn.one : Assn ℕ D).mandNot guardPos) :=
  DerivTot.whileLoop rank decDeriv

/-- **L-7b, unfolded**: *all* the initial mass terminates, in a state where
the counter has reached `0`. -/
theorem countdown_mass_le (s : CQState ℕ D) :
    ((s.q.mass : ℝ≥0) : ℝ≥0∞)
      ≤ PostH (Config.init countdown s) ((Assn.one : Assn ℕ D).mandNot guardPos).op := by
  have h := countdownDeriv.sound s
  rwa [expectE_one] at h

end Qhl.Countdown
