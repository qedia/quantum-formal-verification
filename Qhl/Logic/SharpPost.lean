import Qhl.Logic.Soundness
import Qhl.Logic.WpChain
import Qhl.HSpace.ProjectorSum
import Qhl.HSpace.UnitaryIdentification

/-! # Uniqueness of a pure-state postcondition

Two total-validity triples with the same normalized pure input and program
cannot specify different unit-vector projectors. The proof uses expectation
linearity and the existing bound on terminating mass, not program execution
induction or a semantic implementation equation.
-/
namespace Qhl
open Finset
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

private theorem sharp_dSum_mul (r : ℝ≥0∞) (f : CQState σT D → ℝ≥0∞)
    (c : Config σT D) (n : ℕ) :
    dSum (fun t => r * f t) c n = r * dSum f c n := by
  simp only [dSum]
  generalize boundedFront c n = l
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have hd : dVal (fun t => r * f t) a = r * dVal f a := by
      unfold dVal
      split_ifs <;> simp
    rw [hd, mul_add]

/-- The sum of two terminal expectations is bounded by an operator bound
on their sum and the initial mass. -/
theorem PostH_add_le_scalar_mass (A B : Assn σT D) (r : ℝ) (hr : 0 ≤ r)
    (hbound : ∀ σ, A.op σ + B.op σ ≤ (r : ℂ) • (1 : EndM D univ))
    (c : Config σT D) :
    PostH c A.op + PostH c B.op ≤ ENNReal.ofReal r * (c.mass : ℝ≥0∞) := by
  have hp (s : CQState σT D) :
      expectE A.op s + expectE B.op s ≤ ENNReal.ofReal r * (s.q.mass : ℝ≥0∞) := by
    have hadd : expect (fun σ => A.op σ + B.op σ) s = expect A.op s + expect B.op s := by
      simp only [expect, LinearMap.comp_add, map_add, Complex.add_re]
    have hscalar : expectE (fun _ => (r : ℂ) • (1 : EndM D univ)) s =
        ENNReal.ofReal r * (s.q.mass : ℝ≥0∞) := by
      rw [expectE, expect, LinearMap.comp_smul, Module.End.one_eq_id, LinearMap.comp_id,
        map_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      rw [← PDensity.coe_mass, ENNReal.ofReal_mul hr, ENNReal.ofReal_coe_nnreal]
    rw [expectE, expectE,
      ← ENNReal.ofReal_add (expect_nonneg A.isPositive s) (expect_nonneg B.isPositive s),
      ← hadd]
    exact (expectE_mono hbound s).trans_eq hscalar
  calc
    PostH c A.op + PostH c B.op ≤ ENNReal.ofReal r * TermH c := by
      rw [PostH_eq_tsum A.isPositive, PostH_eq_tsum B.isPositive,
        ← ENNReal.tsum_add, TermH_eq_tsum, ← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro n
      rw [postAtE, postAtE, ← dSum_add, termMassE, ← sharp_dSum_mul]
      exact dSum_mono hp c n
    _ ≤ ENNReal.ofReal r * (c.mass : ℝ≥0∞) :=
      mul_le_mul le_rfl (terminatingTraceMass_le c) bot_le bot_le

/-- Two unit pure-state outputs specified by total validity from the same
unit pure input and the same program have equal projectors. -/
theorem validTot_pure_post_unique (σ : σT) (P : Prog σT D)
    (w u v : HS D (univ : Finset L)) (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hU : validTot (Assn.ofState w hw) P (Assn.ofState u hu))
    (hV : validTot (Assn.ofState w hw) P (Assn.ofState v hv)) :
    outerLM u u = outerLM v v := by
  have he : expectE (Assn.ofState (σT := σT) w hw).op ⟨σ, PDensity.pure w⟩ = 1 := by
    rw [expectE_pure, Assn.ofState_op, outerLM_apply]
    simp [inner_smul_right, inner_self_eq_norm_sq_to_K, hw]
  have hU' := hU ⟨σ, PDensity.pure w⟩
  have hV' := hV ⟨σ, PDensity.pure w⟩
  rw [he] at hU' hV'
  have hsum := PostH_add_le_scalar_mass (Assn.ofState u hu) (Assn.ofState v hv)
    (1 + ‖⟪u, v⟫‖) (by positivity)
    (fun _ => outerLM_self_add_le u v hu hv) (Config.init P ⟨σ, PDensity.pure w⟩)
  have hm : (Config.init P ⟨σ, PDensity.pure w⟩).mass = 1 := PDensity.mass_pure hw
  rw [hm, ENNReal.coe_one, mul_one] at hsum
  have htwo : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + ‖⟪u, v⟫‖) := by
    calc
      (2 : ℝ≥0∞) = 1 + 1 := by norm_num
      _ ≤ _ := (add_le_add hU' hV').trans hsum
  have hreal : (2 : ℝ) ≤ 1 + ‖⟪u, v⟫‖ := by
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (by simpa using htwo)
  have hcs : ‖⟪u, v⟫‖ ≤ 1 := by simpa [hu, hv] using norm_inner_le_norm u v
  exact outerLM_eq_of_norm_inner_eq_one u v hu hv (by linarith)

/-- Derivation-level inputs imply uniqueness through soundness. -/
theorem DerivTot.pure_post_unique (σ : σT) {P : Prog σT D}
    {w u v : HS D (univ : Finset L)} {hw : ‖w‖ = 1} {hu : ‖u‖ = 1} {hv : ‖v‖ = 1}
    (hU : DerivTot (Assn.ofState w hw) P (Assn.ofState u hu))
    (hV : DerivTot (Assn.ofState w hw) P (Assn.ofState v hv)) :
    outerLM u u = outerLM v v :=
  validTot_pure_post_unique σ P w u v hw hu hv hU.sound hV.sound

end Qhl
