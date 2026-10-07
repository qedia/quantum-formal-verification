import Qhl.Foundations.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Identifying isometries from pure-state projectors

Basis projectors together with one unit vector having no zero basis coefficient
identify an isometry up to a common phase.
-/

namespace Qhl
open scoped ComplexInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Equal projectors of unit vectors identify their vectors up to phase. -/
theorem exists_phase_of_outerLM_self_eq (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : outerLM u u = outerLM v v) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ u = c • v := by
  have huu : ⟪u, u⟫ = (1 : ℂ) := by simp [inner_self_eq_norm_sq_to_K, hu]
  have heq : u = ⟪v, u⟫ • v := by
    have hh := congrArg (fun T : E →ₗ[ℂ] E => T u) h
    simpa only [outerLM_apply, huu, one_smul] using hh
  refine ⟨⟪v, u⟫, ?_, heq⟩
  have hn := congrArg norm heq
  simpa only [hu, norm_smul, hv, mul_one] using hn.symm

/-- Equality in Cauchy--Schwarz for unit vectors identifies their projectors. -/
theorem outerLM_eq_of_norm_inner_eq_one (u v : E) (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (h : ‖⟪u, v⟫‖ = 1) :
    outerLM u u = outerLM v v := by
  have hu0 : u ≠ 0 := by intro hz; simp [hz] at hu
  have hv0 : v ≠ 0 := by intro hz; simp [hz] at hv
  obtain ⟨c, _, heq⟩ := (norm_inner_eq_norm_iff hu0 hv0).mp (by simpa [hu, hv] using h)
  have hc : ‖c‖ = 1 := by
    have hn := congrArg norm heq
    simpa only [hv, norm_smul, hu, mul_one] using hn.symm
  rw [heq, outerLM_smul_left, outerLM_smul_right, smul_smul]
  have hphase : c * star c = (1 : ℂ) := by
    change c * starRingEnd ℂ c = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  rw [hphase, one_smul]

/-- One vector with all basis coefficients nonzero fixes the relative phases
left undetermined by the individual basis projectors. -/
theorem isometry_eq_phase_of_basis_projectors {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (V U : E →ₗ[ℂ] F)
    (hV : IsIsometryOp V) (hU : IsIsometryOp U)
    (s : E) (hs : ‖s‖ = 1) (hcoeff : ∀ i, ⟪b i, s⟫ ≠ 0)
    (hb : ∀ i, outerLM (V (b i)) (V (b i)) = outerLM (U (b i)) (U (b i)))
    (hsproj : outerLM (V s) (V s) = outerLM (U s) (U s)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ V = c • U := by
  classical
  have hnV := (LinearMap.norm_map_iff_inner_map_map V).mpr hV
  have hnU := (LinearMap.norm_map_iff_inner_map_map U).mpr hU
  obtain ⟨c, hc, hcs⟩ := exists_phase_of_outerLM_self_eq (V s) (U s)
    (by rw [hnV, hs]) (by rw [hnU, hs]) hsproj
  have hbi : ∀ i, ∃ d : ℂ, ‖d‖ = 1 ∧ V (b i) = d • U (b i) := by
    intro i
    exact exists_phase_of_outerLM_self_eq _ _
      (by rw [hnV]; exact b.orthonormal.norm_eq_one i)
      (by rw [hnU]; exact b.orthonormal.norm_eq_one i) (hb i)
  choose d hd hdi using hbi
  have hsame : ∀ i, d i = c := by
    intro i
    have hexpand : V s = ∑ j, ⟪b j, s⟫ • (d j • U (b j)) := by
      conv_lhs => rw [← b.sum_repr' s]
      simp only [map_sum, map_smul, hdi]
    have hh := congrArg (fun v : F => ⟪U (b i), v⟫) hcs
    rw [hexpand] at hh
    have hinner : ∀ x y, ⟪U x, U y⟫ = ⟪x, y⟫ := hU
    simp only [inner_sum, inner_smul_right, hinner, b.inner_eq_ite] at hh
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true] at hh
    exact mul_left_cancel₀ (hcoeff i) (by simpa only [mul_comm] using hh)
  refine ⟨c, hc, ?_⟩
  apply b.toBasis.ext
  intro i
  simpa only [OrthonormalBasis.coe_toBasis, LinearMap.smul_apply, hsame] using hdi i

/-- The identified isometries give the same projector on every input. -/
theorem outerLM_isometry_eq_of_basis_projectors {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (V U : E →ₗ[ℂ] F)
    (hV : IsIsometryOp V) (hU : IsIsometryOp U)
    (s : E) (hs : ‖s‖ = 1) (hcoeff : ∀ i, ⟪b i, s⟫ ≠ 0)
    (hb : ∀ i, outerLM (V (b i)) (V (b i)) = outerLM (U (b i)) (U (b i)))
    (hsproj : outerLM (V s) (V s) = outerLM (U s) (U s)) (ψ : E) :
    outerLM (V ψ) (V ψ) = outerLM (U ψ) (U ψ) := by
  obtain ⟨c, hc, rfl⟩ := isometry_eq_phase_of_basis_projectors b V U hV hU
    s hs hcoeff hb hsproj
  simp only [LinearMap.smul_apply, outerLM_smul_left, outerLM_smul_right, smul_smul]
  have hphase : c * starRingEnd ℂ c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  change (starRingEnd ℂ c * c) • outerLM (U ψ) (U ψ) = _
  rw [mul_comm, hphase, one_smul]

end Qhl
