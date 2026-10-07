import Qhl.Examples.BoundedRUSTriple

/-! Regression checks for the manuscript's read-only classical RUS bound. -/
namespace Qhl.RUSClassicalCheck
open Qhl.HeraldedRUS Qhl.BoundedRUS Qhl.TwoQubits
open scoped ComplexInnerProductSpace

-- The same program reads its guard from the store, rather than a fixed Lean bound.
example : ClassicalInput.guard (1, true, 1) = false := rfl
example : ClassicalInput.guard (2, true, 1) = true := rfl
example : ClassicalInput.rank (1, true, 2) = -1 := rfl

example : boundedRusClassicalProg =
    Prog.seq (.assign ClassicalInput.initM)
      (.seq (.assign ClassicalInput.initK)
        (.while ClassicalInput.guard
          (.seq (.init fun _ => regA.sig)
            (.seq (.unitary 2 ClassicalInput.rAT (ClassicalInput.gateW wPS))
              (.seq (.measure 2 1 ClassicalInput.rA ClassicalInput.measA ClassicalInput.updM)
                (.assign ClassicalInput.incK)))))) := rfl

example : boundedRusClassicalProg.PreservesParameters
    (fun σ : ℕ × (Bool × ℕ) => σ.1) := boundedRusClassical_preserves_bound

-- State the classical endpoints independently of the named assertions.
example (ψ : 𝕢) (hψ : ‖ψ‖ = 1) :
    (ClassicalInput.pre ψ hψ).classical = (fun σ => 1 ≤ σ.1) := rfl
example (ψ : 𝕢) (hψ : ‖ψ‖ = 1) :
    (ClassicalInput.post vPS ψ hψ).classical =
      (fun σ => σ.2.1 = false ∨ σ.1 ≤ σ.2.2) := rfl
example (ψ : 𝕢) (hψ : ‖ψ‖ = 1) :
    (ClassicalInput.preQ betaPS norm_betaPS_le_one ψ hψ).classical =
      (fun σ => 1 ≤ σ.1) := rfl
example (ψ : 𝕢) (hψ : ‖ψ‖ = 1) :
    (ClassicalInput.postQ vPS ψ hψ).classical = (fun σ => σ.2.1 = false) := rfl

/-- The intended input remains nonvacuous for every positive stored bound. -/
theorem pre_expect_one (ψ : 𝕢) (hψ : ‖ψ‖ = 1) (N : ℕ) (hN : 1 ≤ N) :
    expectE (ClassicalInput.pre ψ hψ).toAssn.op
      (⟨(N, true, 0), (inputState ψ).q⟩ : CQState ClassicalInput.Store D) = 1 := by
  change expectE ((ClassicalInput.effect (fun _ => heraldPre ψ hψ)).mask
    (fun σ : ClassicalInput.Store => 1 ≤ σ.1 ∧ True)).op _ = 1
  rw [expectE, expect, Assn.mask_op_of_pos (φ := fun σ : ClassicalInput.Store =>
    1 ≤ σ.1 ∧ True) (σ := (N, true, 0)) ⟨hN, trivial⟩]
  exact boundedRusPre_expect_one hψ

/-- The positive-budget coefficient is the same quantitative guarantee as before. -/
theorem success_expect (ψ : 𝕢) (hψ : ‖ψ‖ = 1) (N : ℕ) (hN : 1 ≤ N) :
    expectE (ClassicalInput.preQ betaPS norm_betaPS_le_one ψ hψ).toAssn.op
      (⟨(N, true, 0), (inputState ψ).q⟩ : CQState ClassicalInput.Store D) =
      ENNReal.ofReal (1 - (1 / 4 : ℝ) ^ N) := by
  change expectE ((ClassicalInput.effect
    (fun N => heraldPreQ betaPS norm_betaPS_le_one N ψ hψ)).mask
      (fun σ : ClassicalInput.Store => 1 ≤ σ.1 ∧ True)).op _ = _
  rw [expectE, expect, Assn.mask_op_of_pos (φ := fun σ : ClassicalInput.Store =>
    1 ≤ σ.1 ∧ True) (σ := (N, true, 0)) ⟨hN, trivial⟩]
  exact boundedRusSuccessPre_expect hψ N

#print axioms pre_expect_one
#print axioms success_expect
end Qhl.RUSClassicalCheck
