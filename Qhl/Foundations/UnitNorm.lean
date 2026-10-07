import Mathlib.Analysis.Normed.Group.Basic

/-!
# Unit-norm automation for state families

Every product-state triple of this library carries the side condition "each
factor of this family is a unit vector" (`norm_prodV_eq_one`,
`Qhl/Logic/ForRule.lean`). The stage-indexed families that loop invariants are
built from are made in exactly two ways — by **updating** one cell of an
already-unit family, and by a **case split** on the stage guard — so two generic
lemmas discharge every such obligation in one call.

* `norm_update_unit_eq_one` mirrors the `tenvm`/`tentv` norm side conditions of
  CoqQ's `hstensor.v` for a tuple with one component replaced;
* `norm_ite_eq_one` / `norm_dite_eq_one` mirror the automatic discharge of
  `normv v = 1` through `case: ifP` in CoqQ's `mxpred.v`.

Both are stated for an arbitrary normed group and an arbitrary index type: no
quantum object, no gate and no program occurs here. `norm_ite_eq_one` and
`norm_dite_eq_one` are `simp` lemmas, so together with the library's
`@[simp] norm_qbit` / `@[simp] norm_phaseKet` a guarded family's norm proof is a
single `simp [<the family>]`.
-/

namespace Qhl

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E]

/-- **Updating one cell of a unit family keeps it unit.** Replacing the factor
at `c` by a unit vector `u` leaves every factor of the family a unit vector.
Since `i` is the last explicit argument, `norm_update_unit_eq_one hψ hu` is already
the `∀ i, ‖…‖ = 1` shape that `norm_prodV_eq_one` expects. -/
theorem norm_update_unit_eq_one [DecidableEq ι] {ψ : ι → E} {c : ι} {u : E}
    (hψ : ∀ i, ‖ψ i‖ = 1) (hu : ‖u‖ = 1) (i : ι) :
    ‖Function.update ψ c u i‖ = 1 := by
  by_cases h : i = c
  · rw [h, Function.update_self]; exact hu
  · rw [Function.update_of_ne h]; exact hψ i

/-- **A branch on a stage guard is unit when both branches are.** The shape of
every "the first `m` cells are already transformed" invariant. -/
@[simp]
theorem norm_ite_eq_one {p : Prop} [Decidable p] {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖if p then u else v‖ = 1 := by
  split <;> assumption

/-- The dependent-branch version of `norm_ite_eq_one`, for invariants whose
branches use the guard's proof. -/
@[simp]
theorem norm_dite_eq_one {p : Prop} [Decidable p] {u : p → E} {v : ¬p → E}
    (hu : ∀ h, ‖u h‖ = 1) (hv : ∀ h, ‖v h‖ = 1) :
    ‖if h : p then u h else v h‖ = 1 := by
  split
  · exact hu _
  · exact hv _

end Qhl
