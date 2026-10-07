import Qhl.Logic.Source.MeasurementFree
import Qhl.Logic.Source.ConvexDerived
import Qhl.Examples.BoundedRUSTriple

/-! # Zero-retry RUS under the scalar convex rules

Empty Convex2 makes the zero-precondition triple derivable. It does not establish
physical success at zero retries: the program still leaves the failure flag set.
This replaces the obstruction for the earlier constructor set.
-/

namespace Qhl.BoundedRUS

open Qhl.HeraldedRUS TwoQubits
open scoped ComplexInnerProductSpace ComplexOrder

/-- The original success precondition: classical True and the exact scaled effect. -/
noncomputable def successSourcePre (N : ℕ) (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :
    SourceAssertion Store D where
  classical := fun _ => True
  defined := fun _ => True
  quantum := heraldPreQ betaPS norm_betaPS_le_one N ψ₀ hψ₀

/-- The original success postcondition has a separate classical `m = 0` component
and the unmasked projector onto `|0⟩ ⊗ Vψ₀`. -/
noncomputable def successSourcePost (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :
    SourceAssertion Store D where
  classical := fun σ => σ.1 = false
  defined := fun _ => True
  quantum :=
    ⟨fun _ => outerLM (gv q0 ((vPS : 𝕢 →ₗ[ℂ] 𝕢) ψ₀))
      (gv q0 ((vPS : 𝕢 →ₗ[ℂ] 𝕢) ψ₀)),
      fun _ => isEffect_outerLM_self (norm_gv_w vPS hψ₀)⟩

/-- Encoding the exact source precondition gives the existing quantitative pre-effect. -/
theorem successSourcePre_toAssn (N : ℕ) (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :
    (successSourcePre N ψ₀ hψ₀).toAssn =
      heraldPreQ betaPS norm_betaPS_le_one N ψ₀ hψ₀ := by
  apply Assn.ext
  funext σ
  simp only [SourceAssertion.toAssn, successSourcePre, Assn.mask, and_self, if_true]

/-- Encoding the separate original classical success condition gives its masked effect. -/
theorem successSourcePost_toAssn (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :
    (successSourcePost ψ₀ hψ₀).toAssn = succPost vPS ψ₀ hψ₀ := by
  apply Assn.ext
  funext σ
  simp only [SourceAssertion.toAssn, successSourcePost, succPost, Assn.mask, and_true]

/-- At zero attempts the exact literal program has a measurement-free execution
from every input store to the armed, zero-count store. -/
theorem boundedRus_zero_measurementFree (σ : Store) :
    MeasurementFreeExec (boundedRusProg 0) σ (true, 0) := by
  unfold boundedRusProg heraldProg
  apply MeasurementFreeExec.seq (MeasurementFreeExec.assign initM σ)
  apply MeasurementFreeExec.seq (MeasurementFreeExec.assign initK (initM σ))
  apply MeasurementFreeExec.whileFalse
  rfl

/-- The zero-retry quantum precondition is exactly zero. -/
theorem successSourcePre_zero (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :
    successSourcePre 0 ψ₀ hψ₀ = SourceAssertion.ofAssn Assn.zero (fun _ => True) := by
  have hq : heraldPreQ betaPS norm_betaPS_le_one 0 ψ₀ hψ₀ = Assn.zero := by
    apply Assn.ext
    funext σ
    norm_num [heraldPreQ_op, succFloor]
  change SourceAssertion.ofAssn (heraldPreQ betaPS norm_betaPS_le_one 0 ψ₀ hψ₀)
    (fun _ => True) = _
  rw [hq]

/-- Empty Convex2 proves the vacuous zero-retry source triple. -/
theorem successSourceDeriv_zero (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :
    SourceDerivTot (successSourcePre 0 ψ₀ hψ₀) (boundedRusProg 0)
      (successSourcePost ψ₀ hψ₀) := by
  rw [successSourcePre_zero]
  exact SourceDerivTot.zeroPre _ _ _

theorem successSourceDerivPar_zero (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :
    SourceDerivPar (successSourcePre 0 ψ₀ hψ₀) (boundedRusProg 0)
      (successSourcePost ψ₀ hψ₀) := by
  rw [successSourcePre_zero]
  exact SourceDerivPar.zeroPre _ _ _

/-- The all-natural-bound source family combines the empty-weight boundary
case with the existing positive-retry rule derivation. -/
theorem successSourceDeriv_all (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) :
    SourceDerivTot (successSourcePre N ψ₀ hψ₀) (boundedRusProg N)
      (successSourcePost ψ₀ hψ₀) := by
  cases N with
  | zero => exact successSourceDeriv_zero ψ₀ hψ₀
  | succ n => exact boundedRusSuccessSourceDeriv hψ₀ (n + 1) (Nat.succ_pos n)

/-- The original pair is valid through its all-bound source derivation. -/
theorem successSourcePair_valid (N : ℕ) (ψ₀ : 𝕢) (hψ₀ : ‖ψ₀‖ = 1) :
    validTot (successSourcePre N ψ₀ hψ₀).toAssn (boundedRusProg N)
      (successSourcePost ψ₀ hψ₀).toAssn :=
  (successSourceDeriv_all ψ₀ hψ₀ N).sound

/-- The original quantitative semantic endpoints, for every natural retry bound. -/
theorem boundedRusSuccessSourceValid_all {ψ₀ : 𝕢} (hψ₀ : ‖ψ₀‖ = 1) (N : ℕ) :
    validTot (heraldPreQ betaPS norm_betaPS_le_one N ψ₀ hψ₀) (boundedRusProg N)
      (succPost vPS ψ₀ hψ₀) := by
  simpa only [successSourcePre_toAssn, successSourcePost_toAssn] using
    successSourcePair_valid N ψ₀ hψ₀

end Qhl.BoundedRUS

#print axioms Qhl.BoundedRUS.successSourceDeriv_zero
#print axioms Qhl.BoundedRUS.successSourceDeriv_all
#print axioms Qhl.BoundedRUS.successSourcePair_valid
