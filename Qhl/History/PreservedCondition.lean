import Qhl.Program.FrameParameters
import Qhl.Logic.Assertion
import Qhl.History.Approx

/-! # Classical observations preserved through operational histories -/

namespace Qhl

open Finset
open scoped ENNReal

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT E : Type*}

/-- The remaining control preserves a classical observation. -/
def Control.PreservesParameters (e : σT → E) : Control σT D → Prop
  | .done => True
  | .running P => P.PreservesParameters e

/-- Sequencing retains preservation in the residual control. -/
theorem Control.PreservesParameters.seqWith {e : σT → E}
    {c : Control σT D} {Q : Prog σT D}
    (hc : c.PreservesParameters e) (hQ : Q.PreservesParameters e) :
    (c.seqWith Q).PreservesParameters e := by
  cases c with
  | done => exact hQ
  | running P => exact ⟨hc, hQ⟩

/-- Every program step retains the observation and its residual preservation. -/
theorem Prog.PreservesParameters.step_closed {e : σT → E}
    {P : Prog σT D} (hP : P.PreservesParameters e) (σ : σT) (ρ : PDensity D)
    {c : Config σT D} (hc : c ∈ stepProg P σ ρ) :
    e c.cls = e σ ∧ c.ctrl.PreservesParameters e := by
  induction P generalizing σ ρ c with
  | skip => simp only [stepProg, List.mem_singleton] at hc; subst c; exact ⟨rfl, trivial⟩
  | assign f =>
      simp only [stepProg, List.mem_singleton] at hc
      subst c
      exact ⟨hP σ, trivial⟩
  | init S => simp only [stepProg, List.mem_singleton] at hc; subst c; exact ⟨rfl, trivial⟩
  | unitary k r U =>
      simp only [stepProg] at hc
      split_ifs at hc with hi
      · simp only [List.mem_singleton] at hc; subst c; exact ⟨rfl, trivial⟩
      · simp at hc
  | measure m k r M upd =>
      simp only [stepProg] at hc
      split_ifs at hc with hi
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
        exact ⟨hP i σ, trivial⟩
      · simp at hc
  | seq P Q ihP _ =>
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      obtain ⟨he, hp⟩ := ihP hP.1 σ ρ hd
      exact ⟨he, hp.seqWith hP.2⟩
  | ite b P Q _ _ =>
      simp only [stepProg, List.mem_singleton] at hc
      subst c
      refine ⟨rfl, ?_⟩
      change (if b σ then P else Q).PreservesParameters e
      split <;> [exact hP.1; exact hP.2]
  | «while» b P _ =>
      simp only [stepProg] at hc
      split_ifs at hc with hb
      · simp only [List.mem_singleton] at hc
        subst c
        exact ⟨rfl, ⟨hP, hP⟩⟩
      · simp only [List.mem_singleton] at hc
        subst c
        exact ⟨rfl, trivial⟩

/-- A single configuration step preserves the observation and residual control. -/
theorem Control.PreservesParameters.next_closed {e : σT → E}
    {c d : Config σT D} (hc : c.ctrl.PreservesParameters e) (hd : d ∈ next c) :
    e d.cls = e c.cls ∧ d.ctrl.PreservesParameters e := by
  obtain ⟨ctrl, σ, ρ⟩ := c
  cases ctrl with
  | done => simp [next] at hd
  | running P => exact Prog.PreservesParameters.step_closed hc σ ρ hd

/-- Every bounded frontier configuration preserves the root observation. -/
theorem Control.PreservesParameters.boundedFront_closed {e : σT → E}
    {c d : Config σT D} (hc : c.ctrl.PreservesParameters e)
    {n : ℕ} (hd : d ∈ boundedFront c n) :
    e d.cls = e c.cls ∧ d.ctrl.PreservesParameters e := by
  induction n generalizing d with
  | zero =>
      simp only [boundedFront_zero, List.mem_singleton] at hd
      subst d
      exact ⟨rfl, hc⟩
  | succ n ih =>
      rw [boundedFront_succ] at hd
      obtain ⟨u, hu, hd'⟩ := List.mem_flatMap.mp hd
      obtain ⟨he, hp⟩ := ih hu
      obtain ⟨he', hp'⟩ := hp.next_closed hd'
      exact ⟨he'.trans he, hp'⟩

/-- If the root satisfies a preserved predicate, every bounded post-expectation
has the same value with or without the corresponding postcondition mask. -/
theorem postAtE_mask_of_preserved {d : σT → Prop} {c : Config σT D}
    (hc : c.ctrl.PreservesParameters d) (hd : d c.cls) (B : Assn σT D) (n : ℕ) :
    postAtE c n (B.mask d).op = postAtE c n B.op := by
  unfold postAtE dSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  have hdu : d u.cls := (hc.boundedFront_closed hu).1 ▸ hd
  unfold dVal
  by_cases ht : u.isDone = true
  · simp only [if_pos ht]
    exact expectE_mask_of_pos (A := B) (φ := d) (s := u.st) hdu
  · simp only [if_neg ht]

/-- Whole-history post-expectation is unchanged by a preserved true mask. -/
theorem PostH_mask_of_preserved {d : σT → Prop} {c : Config σT D}
    (hc : c.ctrl.PreservesParameters d) (hd : d c.cls) (B : Assn σT D) :
    PostH c (B.mask d).op = PostH c B.op := by
  rw [PostH_eq_tsum (fun σ => (B.mask d).isPositive σ),
    PostH_eq_tsum (fun σ => B.isPositive σ)]
  exact tsum_congr fun n => postAtE_mask_of_preserved hc hd B n

/-- Total correctness survives a preserved classical mask on both sides. -/
theorem validTot_mask_preserved {d : σT → Prop} {P : Prog σT D}
    {A B : Assn σT D} (hp : P.PreservesParameters d)
    (h : validTot A P B) : validTot (A.mask d) P (B.mask d) := by
  intro s
  by_cases hd : d s.cls
  · rw [expectE_mask_of_pos hd,
      PostH_mask_of_preserved (c := Config.init P s) hp hd B]
    exact h s
  · rw [expectE_mask_of_neg hd]
    exact zero_le

/-- Partial correctness survives the same preserved classical mask. -/
theorem validPar_mask_preserved {d : σT → Prop} {P : Prog σT D}
    {A B : Assn σT D} (hp : P.PreservesParameters d)
    (h : validPar A P B) : validPar (A.mask d) P (B.mask d) := by
  intro s
  by_cases hd : d s.cls
  · rw [expectE_mask_of_pos hd,
      PostH_mask_of_preserved (c := Config.init P s) hp hd B]
    exact h s
  · rw [expectE_mask_of_neg hd]
    exact zero_le

end Qhl
