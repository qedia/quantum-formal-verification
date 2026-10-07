import Qhl.History.Approx
import Qhl.Logic.Assertion
import Qhl.Program.KrausFrame

/-! # Transport of bounded histories through a structurally framed Kraus operator -/

namespace Qhl

open Finset
open scoped ENNReal

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

/-- Every configuration on a bounded frontier retains the frame conditions. -/
theorem Control.KrausFrame.boundedFront_closed
    {K : σT → EndM D (univ : Finset L)} {c d : Config σT D}
    (hc : c.ctrl.KrausFrame K) {n : ℕ} (hd : d ∈ boundedFront c n) :
    d.ctrl.KrausFrame K := by
  induction n generalizing d with
  | zero =>
      simp only [boundedFront_zero, List.mem_singleton] at hd
      subst d
      exact hc
  | succ n ih =>
      rw [boundedFront_succ] at hd
      obtain ⟨e, he, hd'⟩ := List.mem_flatMap.mp hd
      exact (ih he).next_closed hd'

/-- Bounded execution commutes with the same Kraus conjugation at every depth. -/
theorem Control.KrausFrame.boundedFront_map
    {K : σT → EndM D (univ : Finset L)} {c : Config σT D}
    (hc : c.ctrl.KrausFrame K) (n : ℕ) :
    boundedFront (c.krausMap K) n = (boundedFront c n).map (Config.krausMap K) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [boundedFront_succ, ih, List.flatMap_map, boundedFront_succ]
      rw [List.map_flatMap]
      apply List.flatMap_congr
      intro d hd
      exact (hc.boundedFront_closed hd).next_map

/-- A terminal-weight sum transports through the framed Kraus operator. -/
theorem Control.KrausFrame.dSum_map
    {K : σT → EndM D (univ : Finset L)} {c : Config σT D}
    (hc : c.ctrl.KrausFrame K) (h : CQState σT D → ℝ≥0∞) (n : ℕ) :
    dSum h (c.krausMap K) n =
      dSum (fun t => h ⟨t.cls, t.q.conj (K t.cls)⟩) c n := by
  rw [dSum, hc.boundedFront_map n, dSum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  simp only [Function.comp_apply, dVal, Config.krausMap_isDone]
  rfl

/-- Framed execution transports post-expectation to the conjugated effect. -/
theorem Control.KrausFrame.PostH_map
    {K : σT → EndM D (univ : Finset L)} {c : Config σT D}
    (hc : c.ctrl.KrausFrame K) (B : Assn σT D) :
    PostH (c.krausMap K) B.op =
      PostH c (fun σ => LinearMap.adjoint (K σ) ∘ₗ B.op σ ∘ₗ K σ) := by
  have hB : ∀ σ, (B.op σ).IsPositive := fun σ => (B.isEffect σ).isPositive
  have hBK : ∀ σ, (LinearMap.adjoint (K σ) ∘ₗ B.op σ ∘ₗ K σ).IsPositive :=
    fun σ => (hB σ).adjoint_conj (K σ)
  rw [PostH_eq_tsum hB, PostH_eq_tsum hBK]
  apply tsum_congr
  intro n
  rw [postAtE, hc.dSum_map (expectE B.op) n, postAtE]
  apply dSum_congr
  intro t
  change ENNReal.ofReal (expect B.op ⟨t.cls, t.q.conj (K t.cls)⟩) = _
  rw [← expect_conj B.op (K t.cls) t.cls t]
  rfl

end Qhl
