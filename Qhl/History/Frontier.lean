import Qhl.History.Occurrence

/-!
# T-2: frontiers of the history tree

Subgoal T-2 of spec 06 (master `HistoryFrontier.lean:58`,
`…DenotationEquivalence.lean`).

`HistFront root n` enumerates *all* occurrence-indexed histories of length `n`
out of `root`, in the order induced by `next`; `TerminalHistFront root n`
keeps the terminated ones. The bridge to the naive iteration of `next` is
`histFront_map_fst`: forgetting the history of a frontier element gives back
the plain bounded iteration `boundedFront`, so nothing is lost or duplicated
by working proof-relevantly.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-- T-2: the frontier at depth `n`: all histories of length `n` from `root`,
paired with the configuration they reach. -/
noncomputable def HistFront (root : Config σT D) :
    (n : ℕ) → List (Σ c : Config σT D, HistFrom root n c)
  | 0 => [⟨root, .nil⟩]
  | n + 1 => (HistFront root n).flatMap fun x =>
      (List.finRange (next x.1).length).map fun i => ⟨_, x.2.step (BranchOcc.of x.1 i)⟩

@[simp]
theorem histFront_zero (root : Config σT D) :
    HistFront root 0 = [⟨root, .nil⟩] := rfl

theorem histFront_succ (root : Config σT D) (n : ℕ) :
    HistFront root (n + 1) = (HistFront root n).flatMap fun x =>
      (List.finRange (next x.1).length).map fun i =>
        ⟨_, x.2.step (BranchOcc.of x.1 i)⟩ := rfl

/-- The plain bounded iteration of `next` (master's
`boundedIterativeDenotation`). -/
noncomputable def boundedFront (root : Config σT D) : ℕ → List (Config σT D)
  | 0 => [root]
  | n + 1 => (boundedFront root n).flatMap next

@[simp]
theorem boundedFront_zero (root : Config σT D) : boundedFront root 0 = [root] := rfl

@[simp]
theorem boundedFront_succ (root : Config σT D) (n : ℕ) :
    boundedFront root (n + 1) = (boundedFront root n).flatMap next := rfl

/-- T-2: the projection equivalence — the frontier and the plain bounded
iteration agree, occurrence by occurrence. -/
theorem histFront_map_fst (root : Config σT D) (n : ℕ) :
    (HistFront root n).map Sigma.fst = boundedFront root n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [histFront_succ, boundedFront_succ, ← ih, List.map_flatMap, List.flatMap_map]
      refine List.flatMap_congr fun x _ => ?_
      simp only [List.map_map, Function.comp_def, BranchOcc.of_target]
      exact List.map_get_finRange (next x.1)

/-- The number of histories at depth `n` is the number of configurations of
the bounded iteration. -/
theorem length_histFront (root : Config σT D) (n : ℕ) :
    (HistFront root n).length = (boundedFront root n).length := by
  rw [← histFront_map_fst, List.length_map]

/-- T-2: the terminated part of a frontier. -/
noncomputable def TerminalHistFront (root : Config σT D) (n : ℕ) :
    List (Σ c : Config σT D, HistFrom root n c) :=
  (HistFront root n).filter fun x => x.1.isDone

theorem terminalHistFront_subset (root : Config σT D) (n : ℕ) :
    ∀ x ∈ TerminalHistFront root n, x ∈ HistFront root n := fun _ hx =>
  List.mem_of_mem_filter hx

theorem isDone_of_mem_terminal {root : Config σT D} {n : ℕ}
    {x : Σ c : Config σT D, HistFrom root n c} (hx : x ∈ TerminalHistFront root n) :
    x.1.isDone = true := by
  simpa using (List.of_mem_filter hx)

end Qhl
