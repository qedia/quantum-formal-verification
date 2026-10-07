import Qhl.Program.FrameParameters
import Qhl.Program.StoreLens

/-! # An added classical ghost is unchanged by a transported program -/

namespace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT V : Type*}

/-- Transport through the first-projection lens never writes the ghost component.
In particular, an integer used as the source total-loop comparison variable stays
fixed throughout execution, rather than being an assumption about the final state. -/
theorem Prog.mapStore_fst_preserves_ghost (P : Prog σT D) :
    (P.mapStore (StoreLens.fst (R := V))).PreservesParameters Prod.snd := by
  induction P with
  | skip => trivial
  | assign f => intro σ; rfl
  | init S => trivial
  | unitary k r U => trivial
  | measure m k r M upd => intro i σ; rfl
  | seq P Q ihP ihQ => exact ⟨ihP, ihQ⟩
  | ite b P Q ihP ihQ => exact ⟨ihP, ihQ⟩
  | «while» b P ih => exact ih

end Qhl
