import Qhl.Logic.Source.BasicDerived
import Qhl.Logic.SharpPost

/-! Projector uniqueness as a mathematical consequence of source derivations. -/
namespace Qhl
open Finset
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

/-- Two source proofs from the same pure input determine the same pure output projector. -/
theorem SourceDerivTot.pure_post_unique (σ : σT) {P : Prog σT D}
    {w u v : HS D (univ : Finset L)} {hw : ‖w‖ = 1} {hu : ‖u‖ = 1} {hv : ‖v‖ = 1}
    (hU : SourceDerivTot (SourceAssertion.ofAssn (Assn.ofState w hw) (fun _ => True)) P
      (SourceAssertion.ofAssn (Assn.ofState u hu) (fun _ => True)))
    (hV : SourceDerivTot (SourceAssertion.ofAssn (Assn.ofState w hw) (fun _ => True)) P
      (SourceAssertion.ofAssn (Assn.ofState v hv) (fun _ => True))) :
    outerLM u u = outerLM v v := by
  apply validTot_pure_post_unique σ P w u v hw hu hv
  · simpa only [SourceAssertion.toAssn_ofAssn_true] using hU.sound
  · simpa only [SourceAssertion.toAssn_ofAssn_true] using hV.sound
end Qhl
