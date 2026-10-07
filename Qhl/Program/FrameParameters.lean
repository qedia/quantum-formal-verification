import Qhl.Program.KrausFrame

/-! # Unchanged classical parameters and disjoint quantum operands -/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT E : Type*}

/-- All assignments and measurement writes preserve the indicated parameters. -/
def Prog.PreservesParameters (e : σT → E) : Prog σT D → Prop
  | .skip => True
  | .assign f => ∀ σ, e (f σ) = e σ
  | .init _ => True
  | .unitary _ _ _ => True
  | .measure _ _ _ _ upd => ∀ i σ, e (upd i σ) = e σ
  | .seq P Q => P.PreservesParameters e ∧ Q.PreservesParameters e
  | .ite _ P Q => P.PreservesParameters e ∧ Q.PreservesParameters e
  | .while _ P => P.PreservesParameters e

/-- Every primitive quantum operation is disjoint from the indicated register. -/
def Prog.AvoidsRegister (S : σT → Finset L) : Prog σT D → Prop
  | .skip => True
  | .assign _ => True
  | .init T => ∀ σ, Disjoint (S σ) (T σ)
  | .unitary _ r _ => ∀ σ, Disjoint (S σ) (univ.image (r σ))
  | .measure _ _ r _ _ => ∀ σ, Disjoint (S σ) (univ.image (r σ))
  | .seq P Q => P.AvoidsRegister S ∧ Q.AvoidsRegister S
  | .ite _ P Q => P.AvoidsRegister S ∧ Q.AvoidsRegister S
  | .while _ P => P.AvoidsRegister S

/-- Source locality and unchanged parameter values establish the structural
frame hypothesis for an arbitrary operator on the accumulating register. -/
theorem Prog.krausFrame_of_parameters (P : Prog σT D) (e : σT → E)
    (S : E → Finset L) (f : ∀ a, EndM D (S a))
    (hp : P.PreservesParameters e) (hq : P.AvoidsRegister (fun σ => S (e σ))) :
    P.KrausFrame (fun σ => liftF D (subset_univ (S (e σ))) (f (e σ))) := by
  induction P with
  | skip => trivial
  | assign g =>
    intro σ
    exact congrArg (fun a => liftF D (subset_univ (S a)) (f a)) (hp σ)
  | init T =>
    intro σ
    exact ⟨S (e σ), f (e σ), hq σ, rfl⟩
  | unitary k r U =>
    intro σ
    exact ⟨S (e σ), f (e σ), hq σ, rfl⟩
  | measure m k r M upd =>
    refine ⟨fun σ => ⟨S (e σ), f (e σ), hq σ, rfl⟩, ?_⟩
    intro i σ
    exact congrArg (fun a => liftF D (subset_univ (S a)) (f a)) (hp i σ)
  | seq P Q ihP ihQ => exact ⟨ihP hp.1 hq.1, ihQ hp.2 hq.2⟩
  | ite b P Q ihP ihQ => exact ⟨ihP hp.1 hq.1, ihQ hp.2 hq.2⟩
  | «while» b P ih => exact ih hp hq

/-- Preserving a collection of parameter values preserves any function of them. -/
theorem Prog.PreservesParameters.comp {P : Prog σT D} {e : σT → E}
    (hp : P.PreservesParameters e) {F : Type*} (f : E → F) :
    P.PreservesParameters (fun σ => f (e σ)) := by
  induction P with
  | skip => trivial
  | assign g => intro σ; exact congrArg f (hp σ)
  | init S => trivial
  | unitary k r U => trivial
  | measure m k r M upd => intro i σ; exact congrArg f (hp i σ)
  | seq P Q ihP ihQ => exact ⟨ihP hp.1, ihQ hp.2⟩
  | ite b P Q ihP ihQ => exact ⟨ihP hp.1, ihQ hp.2⟩
  | «while» b P ih => exact ih hp

end Qhl
