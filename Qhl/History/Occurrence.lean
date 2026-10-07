import Qhl.Program.Spec

/-!
# T-1: branch occurrences and occurrence-indexed histories

Subgoal T-1 of spec 06 (master `DirectHistoryOccurrence.lean:29,77`).

The paper's denotational semantics of qWhile⁺ is a *multiset* of terminal
cq-states (Def 3.4). Master's sanctioned deviation — kept here verbatim in
shape (Decision W7) — is to realise the multiset **proof-relevantly**: a
branch of the step relation is an *occurrence* (an index into `next c`, not
just a member of it), and a history is a chain of occurrences. Two branches
that happen to produce the same configuration therefore stay distinct, which
is exactly what a multiset semantics requires.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-- T-1: an occurrence of a one-step branch out of `c`: an *index* into
`next c` together with the configuration it produces. -/
structure BranchOcc (c : Config σT D) where
  /-- Which branch of `next c` this is. -/
  index : Fin (next c).length
  /-- The successor configuration. -/
  target : Config σT D
  /-- The successor is the one the index points at. -/
  target_eq : target = (next c)[index.val]

namespace BranchOcc

variable {c : Config σT D}

/-- The occurrence at a given index. -/
noncomputable def of (c : Config σT D) (i : Fin (next c).length) : BranchOcc c := ⟨i, _, rfl⟩

@[simp]
theorem of_index (c : Config σT D) (i : Fin (next c).length) : (of c i).index = i := rfl

@[simp]
theorem of_target (c : Config σT D) (i : Fin (next c).length) :
    (of c i).target = (next c)[i.val] := rfl

theorem target_mem (o : BranchOcc c) : o.target ∈ next c := by
  rw [o.target_eq]
  exact List.getElem_mem _

/-- Every occurrence is a step of the transition relation. -/
theorem step (o : BranchOcc c) : Step c o.target := o.target_mem

/-- A terminated configuration has no branches. -/
theorem isEmpty_of_done (σ : σT) (ρ : PDensity D) :
    IsEmpty (BranchOcc (⟨.done, σ, ρ⟩ : Config σT D)) :=
  ⟨fun o => absurd o.index.isLt (by simp)⟩

end BranchOcc

/-- T-1: an occurrence-indexed history of length `n` from `root`, ending in a
given configuration. -/
inductive HistFrom (root : Config σT D) : ℕ → Config σT D → Type _ where
  /-- The empty history. -/
  | nil : HistFrom root 0 root
  /-- Extend a history by one branch occurrence. -/
  | step {n : ℕ} {c : Config σT D} (h : HistFrom root n c) (o : BranchOcc c) :
      HistFrom root (n + 1) o.target

namespace HistFrom

variable {root : Config σT D}

/-- The list of configurations visited by a history, oldest first. -/
noncomputable def trace : {n : ℕ} → {c : Config σT D} → HistFrom root n c → List (Config σT D)
  | _, _, .nil => [root]
  | _, _, .step h o => h.trace ++ [o.target]

@[simp]
theorem trace_nil : (HistFrom.nil (root := root)).trace = [root] := rfl

@[simp]
theorem trace_step {n : ℕ} {c : Config σT D} (h : HistFrom root n c) (o : BranchOcc c) :
    (h.step o).trace = h.trace ++ [o.target] := rfl

theorem length_trace : ∀ {n : ℕ} {c : Config σT D} (h : HistFrom root n c),
    h.trace.length = n + 1
  | _, _, .nil => rfl
  | _, _, .step h _ => by simp [length_trace h]

end HistFrom

end Qhl
