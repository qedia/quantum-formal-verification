import Qhl.Logic.StateApproximation

/-! # Classical conditions preserved by a program

A condition on unchanged classical inputs can be retained on both sides of a
Hoare triple. This is derived by scaling effects by its zero/one indicator.
-/

namespace Qhl
open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {σT : Type*} [∀ i, Inhabited (D i)]

/-- Preserve a classical condition using only the existing proof constructors. -/
theorem DerivTot.mask_preserved {A B : Assn σT D} {P : Prog σT D}
    (h : DerivTot A P B) (φ : σT → Prop) (hp : P.Preserves φ) :
    DerivTot (A.mask φ) P (B.mask φ) := by
  classical
  let c : σT → ℝ := fun σ => if φ σ then 1 else 0
  have h0 : ∀ σ, 0 ≤ c σ := fun σ => by simp only [c]; split <;> norm_num
  have h1 : ∀ σ, c σ ≤ 1 := fun σ => by simp only [c]; split <;> norm_num
  have he (C : Assn σT D) : C.scaledBy c h0 h1 = C.mask φ := by
    ext σ
    by_cases hφ : φ σ <;> simp [Assn.scaledBy_op, c, hφ]
  have hc : P.Preserves c := hp.comp (fun p : Prop => if p then (1 : ℝ) else 0)
  simpa only [he] using h.scaledBy c h0 h1 hc

end Qhl
