import Mathlib.Algebra.BigOperators.Fin

/-!
# Guarded partial sums over `Fin k`

The bigop automation every *staged* derivation of this library needs: a loop
that runs `m` of its `k` iterations has accumulated the **guarded** sum
`∑ⱼ [j < m] f j`, and the chain rule asks for that object's three laws — it is
empty at `m = 0`, it is the whole sum once `m` has passed `k`, and it grows by
exactly one summand when `m` increments.

This is the Lean counterpart of the mathcomp/CoqQ bigop toolkit that CoqQ's
`example.v` derivations lean on:

* the guarded summand `if (j : ℕ) < m then f j else 0` is mathcomp
  `big_mkcond`: a filtered big operator written as a full sum;
* `sum_ite_lt_zero` is the degenerate `big_pred0`;
* `sum_ite_lt_of_le` is `big_ord_widen` / `eq_bigl` at an always-true guard;
* `sum_ite_lt_succ` is `big_ord_recr` (peel the last index) with `big_split`.

Everything is stated over an arbitrary `AddCommMonoid`, mentions no quantum
object at all, and is reused by the QFT phase ladder (`qftLadderSum`,
`Qhl/Register/Fourier.lean`) and by any other stage-indexed accumulator.
-/

namespace Qhl

open Finset

variable {M : Type*} [AddCommMonoid M] {k : ℕ}

/-- **The empty stage.** No index is below `0`, so the guarded sum vanishes.
mathcomp `big_pred0`. -/
theorem sum_ite_lt_zero (f : Fin k → M) :
    ∑ j : Fin k, (if (j : ℕ) < 0 then f j else 0) = 0 := by
  simp

/-- **The saturated stage.** Once the guard `m` has reached the width `k` every
index passes it, so the guarded sum is the full sum. mathcomp `big_ord_widen`
/ `eq_bigl` at an always-true predicate. -/
theorem sum_ite_lt_of_le {m : ℕ} (hkm : k ≤ m) (f : Fin k → M) :
    ∑ j : Fin k, (if (j : ℕ) < m then f j else 0) = ∑ j : Fin k, f j :=
  Finset.sum_congr rfl fun j _ => if_pos (lt_of_lt_of_le j.isLt hkm)

/-- **The workhorse: one more stage adds exactly one summand.** Splitting each
guard `(j : ℕ) < m + 1` into `(j : ℕ) < m` and `j = ⟨m, hm⟩` is mathcomp's
`big_ord_recr` (peel off the last index) followed by `big_split`. This is the
arithmetic every chain-rule step of a `for`-fold discharges. -/
theorem sum_ite_lt_succ (f : Fin k → M) {m : ℕ} (hm : m < k) :
    ∑ j : Fin k, (if (j : ℕ) < m + 1 then f j else 0)
      = (∑ j : Fin k, if (j : ℕ) < m then f j else 0) + f ⟨m, hm⟩ := by
  have hmk : ((⟨m, hm⟩ : Fin k) : ℕ) = m := rfl
  have hsplit : ∀ j : Fin k,
      (if (j : ℕ) < m + 1 then f j else 0)
        = (if (j : ℕ) < m then f j else 0) + (if j = (⟨m, hm⟩ : Fin k) then f j else 0) := by
    intro j
    by_cases h2 : j = (⟨m, hm⟩ : Fin k)
    · subst h2
      rw [if_pos (by omega), if_neg (by omega), if_pos rfl, zero_add]
    · have h3 : (j : ℕ) ≠ m := fun hc => h2 (Fin.ext (by omega))
      by_cases h1 : (j : ℕ) < m
      · rw [if_pos (by omega), if_pos h1, if_neg h2, add_zero]
      · rw [if_neg (by omega), if_neg h1, if_neg h2, add_zero]
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_eq' univ (⟨m, hm⟩ : Fin k) f, if_pos (mem_univ _)]

end Qhl
