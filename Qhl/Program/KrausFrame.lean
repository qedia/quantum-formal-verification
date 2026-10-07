import Qhl.Program.LocalConjugation

/-! # Structural conditions for an untouched Kraus operator

The conditions inspect program operations, not its denotation. Local operators
have disjoint actual supports; classical writes preserve the operator family.
These are the interpreted locality and unchanged-parameter conditions used by
the source accumulation rules.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

/-- An operator has a support disjoint from the indicated operation. -/
def DisjointOperator (K : EndM D (univ : Finset L)) (T : Finset L) : Prop :=
  ∃ (S : Finset L) (f : EndM D S),
    Disjoint S T ∧ K = liftF D (subset_univ S) f

/-- Structural locality and classical stability for an operator family. -/
def Prog.KrausFrame (K : σT → EndM D (univ : Finset L)) : Prog σT D → Prop
  | .skip => True
  | .assign f => ∀ σ, K (f σ) = K σ
  | .init S => ∀ σ, DisjointOperator (K σ) (S σ)
  | .unitary _ r _ => ∀ σ, DisjointOperator (K σ) (univ.image (r σ))
  | .measure _ _ r _ upd =>
      (∀ σ, DisjointOperator (K σ) (univ.image (r σ))) ∧
      (∀ i σ, K (upd i σ) = K σ)
  | .seq P Q => P.KrausFrame K ∧ Q.KrausFrame K
  | .ite _ P Q => P.KrausFrame K ∧ Q.KrausFrame K
  | .while _ P => P.KrausFrame K

/-- The remaining control still satisfies the same locality conditions. -/
def Control.KrausFrame (K : σT → EndM D (univ : Finset L)) : Control σT D → Prop
  | .done => True
  | .running P => P.KrausFrame K

/-- Conjugate the quantum state, preserving program control and classical state. -/
noncomputable def Config.krausMap (K : σT → EndM D (univ : Finset L))
    (c : Config σT D) : Config σT D :=
  ⟨c.ctrl, c.cls, c.q.conj (K c.cls)⟩

@[simp]
theorem Config.krausMap_isDone (K : σT → EndM D (univ : Finset L))
    (c : Config σT D) : (c.krausMap K).isDone = c.isDone := rfl

/-- Sequencing preserves the structural frame conditions. -/
theorem Control.KrausFrame.seqWith {K : σT → EndM D (univ : Finset L)}
    {c : Control σT D} {Q : Prog σT D}
    (hc : c.KrausFrame K) (hQ : Q.KrausFrame K) :
    (c.seqWith Q).KrausFrame K := by
  cases c with
  | done => exact hQ
  | running P => exact ⟨hc, hQ⟩

/-- Every one-step successor retains the structural frame conditions. -/
theorem Prog.KrausFrame.step_closed {K : σT → EndM D (univ : Finset L)}
    {P : Prog σT D} (hP : P.KrausFrame K) (σ : σT) (ρ : PDensity D)
    {c : Config σT D} (hc : c ∈ stepProg P σ ρ) : c.ctrl.KrausFrame K := by
  induction P generalizing σ ρ c with
  | skip => simp only [stepProg, List.mem_singleton] at hc; subst c; trivial
  | assign f => simp only [stepProg, List.mem_singleton] at hc; subst c; trivial
  | init S => simp only [stepProg, List.mem_singleton] at hc; subst c; trivial
  | unitary k r U =>
    simp only [stepProg] at hc
    split_ifs at hc with hi
    · simp only [List.mem_singleton] at hc; subst c; trivial
    · simp at hc
  | measure m k r M upd =>
    simp only [stepProg] at hc
    split_ifs at hc with hi
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
      trivial
    · simp at hc
  | seq P Q ihP _ =>
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (ihP hP.1 σ ρ hd).seqWith hP.2
  | ite b P Q _ _ =>
    simp only [stepProg, List.mem_singleton] at hc
    subst c
    change (if b σ then P else Q).KrausFrame K
    split <;> [exact hP.1; exact hP.2]
  | «while» b P _ =>
    simp only [stepProg] at hc
    split_ifs at hc with hb
    · simp only [List.mem_singleton] at hc
      subst c
      exact ⟨hP, hP⟩
    · simp only [List.mem_singleton] at hc; subst c; trivial

/-- One-step execution commutes with conjugation under the structural conditions. -/
theorem Prog.KrausFrame.step_map {K : σT → EndM D (univ : Finset L)}
    {P : Prog σT D} (hP : P.KrausFrame K) (σ : σT) (ρ : PDensity D) :
    stepProg P σ (ρ.conj (K σ)) = (stepProg P σ ρ).map (Config.krausMap K) := by
  induction P generalizing σ ρ with
  | skip => rfl
  | assign f => simp [stepProg, Config.krausMap, hP σ]
  | init T =>
    obtain ⟨S, f, hd, he⟩ := hP σ
    simp only [stepProg, List.map_cons, List.map_nil, Config.krausMap]
    rw [he, PDensity.mapSO_initLift_conj hd]
  | unitary k r U =>
    simp only [stepProg]
    split_ifs with hi
    · obtain ⟨S, f, hd, he⟩ := hP σ
      simp only [List.map_cons, List.map_nil, Config.krausMap]
      rw [he, PDensity.conj_regLift_conj ⟨r σ, hi⟩ hd]
    · rfl
  | measure m k r M upd =>
    simp only [stepProg]
    split_ifs with hi
    · rw [List.map_map]
      apply List.map_congr_left
      intro i _
      obtain ⟨S, f, hd, he⟩ := hP.1 σ
      simp only [Function.comp_apply, Config.krausMap]
      rw [hP.2 i σ, he, PDensity.conj_regLift_conj ⟨r σ, hi⟩ hd]
    · rfl
  | seq P Q ihP _ =>
    simp only [stepProg, ihP hP.1, List.map_map]
    rfl
  | ite b P Q _ _ => rfl
  | «while» b P _ =>
    simp only [stepProg]
    split_ifs <;> rfl

/-- Configuration successors retain locality and stability. -/
theorem Control.KrausFrame.next_closed {K : σT → EndM D (univ : Finset L)}
    {c d : Config σT D} (hc : c.ctrl.KrausFrame K) (hd : d ∈ next c) :
    d.ctrl.KrausFrame K := by
  obtain ⟨ctrl, σ, ρ⟩ := c
  cases ctrl with
  | done => simp [next] at hd
  | running P => exact Prog.KrausFrame.step_closed hc σ ρ hd

/-- Configuration form of one-step covariance. -/
theorem Control.KrausFrame.next_map {K : σT → EndM D (univ : Finset L)}
    {c : Config σT D} (hc : c.ctrl.KrausFrame K) :
    next (c.krausMap K) = (next c).map (Config.krausMap K) := by
  obtain ⟨ctrl, σ, ρ⟩ := c
  cases ctrl with
  | done => rfl
  | running P => exact Prog.KrausFrame.step_map hc σ ρ

end Qhl
