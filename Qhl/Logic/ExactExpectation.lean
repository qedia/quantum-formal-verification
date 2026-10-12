import Qhl.Logic.AlmostSure

/-! Exact expectations obtained from complementary total-correctness bounds. -/
namespace Qhl
open Finset
open scoped ENNReal
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

/-- Two complementary total-validity bounds determine the expectation exactly. -/
theorem PostH_eq_of_complement {A B : Assn σT D} {P : Prog σT D}
    (h : validTot A P B) (hc : validTot A.compl P B.compl)
    (s : CQState σT D) : PostH (Config.init P s) B.op = expectE A.op s := by
  apply le_antisymm ?_ (h s)
  apply ENNReal.le_of_add_le_add_right ((expectE_le_mass' A.compl s).trans_lt ENNReal.coe_lt_top).ne
  calc
    PostH (Config.init P s) B.op + expectE A.compl.op s
      ≤ PostH (Config.init P s) B.op + PostH (Config.init P s) B.compl.op :=
        add_le_add le_rfl (hc s)
    _ = TermH (Config.init P s) := PostH_add_PostH_compl B _
    _ ≤ (s.q.mass : ℝ≥0∞) := terminatingTraceMass_le _
    _ = expectE A.op s + expectE A.compl.op s := (expectE_add_expectE_compl A s).symm

/-- The dual initialization channel preserves effect complements. -/
theorem Assn.initPre_compl (A : Assn σT D) (S : σT → Finset L) :
    A.compl.initPre S = (A.initPre S).compl := by
  apply Assn.ext
  funext σ
  simp only [Assn.initPre_op, Assn.compl_op, map_sub]
  rw [show dualSO D (initLift (S σ)) 1 = 1 from Assn.initPre_one_op S σ]

end Qhl

#print axioms Qhl.PostH_eq_of_complement
#print axioms Qhl.Assn.initPre_compl
