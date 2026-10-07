import Qhl.History.GhostStore
import Qhl.Logic.Source.TotalLoop

/-! # The source total-loop rank as an immutable classical ghost variable -/

namespace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

namespace SourceAssertion

/-- The rank premise precondition with a genuine integer variable in the store. -/
def rankGhostPre (A : SourceAssertion σT D) (b : σT → Bool) (t : σT → Int) :
    SourceAssertion (σT × Int) D :=
  identity (fun p => A.classical p.1 ∧ b p.1 = true ∧ t p.1 = p.2)

/-- The rank premise postcondition compares against the unchanged ghost variable. -/
def rankGhostPost (t : σT → Int) : SourceAssertion (σT × Int) D :=
  identity (fun p => t p.1 < p.2)

/-- Slicing a ghost rank precondition gives the original fixed-parameter premise. -/
theorem rankGhostPre_slice (A : SourceAssertion σT D) (b : σT → Bool)
    (t : σT → Int) (z : Int) :
    (rankGhostPre A b t).toAssn.ghostSlice z =
      (identity (D := D)
        (fun σ => A.classical σ ∧ b σ = true ∧ t σ = z)).toAssn := by
  apply Assn.ext
  funext σ
  rfl

/-- Slicing a ghost rank postcondition gives its fixed-parameter counterpart. -/
theorem rankGhostPost_slice (t : σT → Int) (z : Int) :
    (rankGhostPost (D := D) t).toAssn.ghostSlice z =
      (identity (D := D) (fun σ => t σ < z)).toAssn := by
  apply Assn.ext
  funext σ
  rfl

end SourceAssertion

/-- A genuine integer ghost rank triple is equivalent to all immutable
fixed-parameter rank triples, using the operational map of the loop body. -/
theorem validTot_rankGhost_iff (A : SourceAssertion σT D) (b : σT → Bool)
    (t : σT → Int) (P : Prog σT D) :
    validTot (A.rankGhostPre b t).toAssn
      (P.mapStore (StoreLens.fst (R := Int)))
      (SourceAssertion.rankGhostPost (D := D) t).toAssn ↔
      ∀ z : Int, validTot
        (SourceAssertion.identity (D := D)
          (fun σ => A.classical σ ∧ b σ = true ∧ t σ = z)).toAssn P
        (SourceAssertion.identity (D := D) (fun σ => t σ < z)).toAssn := by
  rw [validTot_mapStore_fst_iff]
  simp only [SourceAssertion.rankGhostPre_slice, SourceAssertion.rankGhostPost_slice]

/-- The original total-loop semantic rule accepts a named integer ghost rank
premise, whose constancy is established by the transported operational semantics. -/
theorem validTot_sourceWhile_ghost {A : SourceAssertion σT D} {b : σT → Bool}
    {P : Prog σT D} (t : σT → Int)
    (hbound : ∀ σ, A.classical σ → 0 ≤ t σ)
    (hInv : validTot
      (A.withClassical fun σ => A.classical σ ∧ b σ = true).toAssn P A.toAssn)
    (hRank : validTot (A.rankGhostPre b t).toAssn
      (P.mapStore (StoreLens.fst (R := Int)))
      (SourceAssertion.rankGhostPost (D := D) t).toAssn) :
    validTot A.toAssn (.while b P)
      (A.withClassical fun σ => A.classical σ ∧ b σ = false).toAssn := by
  rw [SourceAssertion.guard_toAssn, SourceAssertion.toAssn_eq_nested_mask] at hInv
  rw [SourceAssertion.toAssn_eq_nested_mask, SourceAssertion.exit_toAssn]
  have hRank' := (validTot_rankGhost_iff A b t P).mp hRank
  have hRank'' : ∀ z : Int, validTot
      ((Assn.one : Assn σT D).mask
        fun σ => A.classical σ ∧ b σ = true ∧ t σ = z) P
      ((Assn.one : Assn σT D).mask fun σ => t σ < z) := by
    intro z
    simpa only [SourceAssertion.identity_toAssn] using hRank' z
  exact validTot_while_source t hbound hInv hRank''

#print axioms validTot_rankGhost_iff
#print axioms validTot_sourceWhile_ghost

end Qhl
