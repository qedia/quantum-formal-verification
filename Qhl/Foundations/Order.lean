import Qhl.Foundations.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Foundations: Löwner order lemmas and the psd factorization

Spec 01, subgoals F-L5 and F-L6 (CoqQ `quantum.v:2266,2324-2331` and the psd
theory of `mxpred.v`/`quantum.v`).

The defining unfolds of the Löwner order are mathlib's and are reused as-is:
`LinearMap.le_def : f ≤ g ↔ (g - f).IsPositive` and
`LinearMap.nonneg_iff_isPositive : 0 ≤ f ↔ f.IsPositive`.
Likewise congruence of positivity (needed by spec 02's H-20) is mathlib's
`LinearMap.IsPositive.adjoint_conj : (g† ∘ₗ f ∘ₗ g).IsPositive` (and
`.conj_adjoint` for `g ∘ₗ f ∘ₗ g†`).

This file adds:

* `isPositive_iff_inner_nonneg` — over ℂ, `f.IsPositive ↔ ∀ x, 0 ≤ ⟪x, f x⟫`
  (`≤` from the scoped `ComplexOrder`); symmetry of `f` is automatic.
* `le_iff_inner_le` — F-L5, CoqQ `lef_dot`: `f ≤ g ↔ ∀ v, ⟪v, f v⟫ ≤ ⟪v, g v⟫`.
  (With `ComplexOrder`'s `≤` on `ℂ`; the real-part-only version is *not* an
  unconditional iff — e.g. `g = f + Complex.I • 1` satisfies it but `f ≤ g` fails.)
* `trace_re_mono` — F-L5: the real trace is Löwner-monotone.
* `isPositive_adjoint_iff` / `isPositive_conjLM_iff` / `isPositive_transposeLM_iff`
  and `adjoint_le_adjoint_iff` / `conjLM_le_conjLM_iff` /
  `transposeLM_le_transposeLM_iff` — F-L5: positivity and the order are
  preserved by each of A/C/T.
* `isPositive_iff_exists_adjoint_comp` — **F-L6**: `f.IsPositive ↔ ∃ g, f = g† ∘ₗ g`.
  The forward direction goes through the C⋆-algebra `E →L[ℂ] E`
  (`CStarAlgebra.nonneg_iff_eq_star_mul_self`).
-/

namespace Qhl

open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate

/-! ## F-L5: the Löwner order via inner products -/

section Loewner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Over ℂ, positivity is captured by `0 ≤ ⟪x, f x⟫` alone (`≤` from the scoped
`ComplexOrder`): the nonnegativity forces `⟪x, f x⟫` to be real, which over ℂ
already makes `f` symmetric. -/
theorem isPositive_iff_inner_nonneg (f : E →ₗ[ℂ] E) :
    f.IsPositive ↔ ∀ x, 0 ≤ ⟪x, f x⟫ := by
  refine ⟨fun hf x => hf.inner_nonneg_right x, fun h => ?_⟩
  have hreal : ∀ v, conj ⟪v, f v⟫ = ⟪v, f v⟫ := fun v =>
    RCLike.conj_eq_iff_im.mpr (RCLike.nonneg_iff.mp (h v)).2
  refine f.isPositive_iff.mpr
    ⟨f.isSymmetric_iff_inner_map_self_real.mpr fun v => ?_, fun x => ?_⟩
  · rw [← inner_conj_symm (f v) v, hreal, hreal]
  · rw [← inner_conj_symm (f x) x, hreal]
    exact h x

/-- F-L5, CoqQ `lef_dot` (`quantum.v:2266`): the Löwner order via inner
products, with `ComplexOrder`'s `≤` on `ℂ`. -/
theorem le_iff_inner_le (f g : E →ₗ[ℂ] E) :
    f ≤ g ↔ ∀ v, ⟪v, f v⟫ ≤ ⟪v, g v⟫ := by
  rw [LinearMap.le_def, isPositive_iff_inner_nonneg]
  exact forall_congr' fun v => by
    rw [LinearMap.sub_apply, inner_sub_right, sub_nonneg]

/-- F-L5 (CoqQ `quantum.v:2324`): the real trace is monotone for the Löwner
order. (For `f ≤ g` the traces differ by the trace of the positive map `g - f`,
a nonnegative real.) -/
theorem trace_re_mono {f g : E →ₗ[ℂ] E} (h : f ≤ g) :
    (LinearMap.trace ℂ E f).re ≤ (LinearMap.trace ℂ E g).re := by
  have h0 := ((LinearMap.le_def f g).mp h).trace_nonneg
  rw [map_sub, sub_nonneg] at h0
  exact (Complex.le_def.mp h0).1

end Loewner

/-! ## F-L5: the order is preserved by adjoint, conjugation, transposition -/

section Adjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Positivity is preserved by the adjoint (a positive map equals its adjoint). -/
theorem isPositive_adjoint_iff (f : E →ₗ[ℂ] E) :
    (LinearMap.adjoint f).IsPositive ↔ f.IsPositive := by
  constructor
  · intro h
    rw [← LinearMap.adjoint_adjoint f, h.adjoint_eq]
    exact h
  · intro hf
    rw [hf.adjoint_eq]
    exact hf

/-- F-L5 (CoqQ `lef_adj`): the Löwner order is preserved by the adjoint. -/
theorem adjoint_le_adjoint_iff {f g : E →ₗ[ℂ] E} :
    LinearMap.adjoint f ≤ LinearMap.adjoint g ↔ f ≤ g := by
  rw [LinearMap.le_def, LinearMap.le_def, ← map_sub, isPositive_adjoint_iff]

end Adjoint

section ConjTranspose

variable {ι : Type*} [Fintype ι]

private theorem conjLM_sub (f g : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) :
    conjLM (f - g) = conjLM f - conjLM g := by
  refine LinearMap.ext fun v => ?_
  ext i
  simp

/-- Positivity is preserved by basis conjugation. -/
theorem isPositive_conjLM_iff (f : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) :
    (conjLM f).IsPositive ↔ f.IsPositive := by
  have key : ∀ g : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι,
      g.IsPositive → (conjLM g).IsPositive := fun g hg => by
    rw [isPositive_iff_inner_nonneg]
    intro x
    rw [conjLM_apply, inner_conjV_right]
    exact hg.inner_nonneg_left _
  exact ⟨fun h => conjLM_conjLM f ▸ key _ h, key f⟩

/-- F-L5 (CoqQ `lef_conj`): the Löwner order is preserved by basis conjugation. -/
theorem conjLM_le_conjLM_iff {f g : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} :
    conjLM f ≤ conjLM g ↔ f ≤ g := by
  rw [LinearMap.le_def, LinearMap.le_def, ← conjLM_sub, isPositive_conjLM_iff]

/-- Positivity is preserved by transposition. -/
theorem isPositive_transposeLM_iff (f : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) :
    (transposeLM f).IsPositive ↔ f.IsPositive := by
  rw [← adjoint_conjLM, isPositive_adjoint_iff, isPositive_conjLM_iff]

/-- F-L5 (CoqQ `lef_tr`): the Löwner order is preserved by transposition. -/
theorem transposeLM_le_transposeLM_iff
    {f g : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι} :
    transposeLM f ≤ transposeLM g ↔ f ≤ g := by
  rw [← adjoint_conjLM, ← adjoint_conjLM, adjoint_le_adjoint_iff, conjLM_le_conjLM_iff]

end ConjTranspose

/-! ## F-L6: the psd factorization -/

section Factorization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- **F-L6** (CoqQ psd factorization): a map is positive iff it factors as
`g† ∘ₗ g`. Feeds spec 02's H-21 (positivity of the labelled tensor). -/
theorem isPositive_iff_exists_adjoint_comp (f : E →ₗ[ℂ] E) :
    f.IsPositive ↔ ∃ g : E →ₗ[ℂ] E, f = LinearMap.adjoint g ∘ₗ g := by
  refine ⟨fun hf => ?_,
    fun ⟨g, hg⟩ => by rw [hg]; exact LinearMap.isPositive_adjoint_comp_self g⟩
  have := FiniteDimensional.complete ℂ E
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (f.isPositive_toContinuousLinearMap_iff.mpr hf))
  refine ⟨B.toLinearMap, LinearMap.ext fun x => ?_⟩
  have hx := DFunLike.congr_fun hB x
  simpa [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_toLinearMap] using hx

/-- The trace pairing of two positive operators is nonnegative (`≤` from the
scoped `ComplexOrder`). Spec 04 support (Q-5): via the F-L6 factorization
`f = g† ∘ g` and trace cyclicity. -/
theorem trace_comp_nonneg {f g : E →ₗ[ℂ] E} (hf : f.IsPositive) (hg : g.IsPositive) :
    0 ≤ LinearMap.trace ℂ E (f ∘ₗ g) := by
  obtain ⟨h, rfl⟩ := (isPositive_iff_exists_adjoint_comp f).mp hf
  rw [LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  exact (hg.conj_adjoint h).trace_nonneg

/-- Monotonicity of the trace pairing against a positive operator: for
`f` positive and `A ≤ B` (Löwner), `Tr (f ∘ A) ≤ Tr (f ∘ B)`.
Spec 04 support (Q-5). -/
theorem trace_comp_mono {f A B : E →ₗ[ℂ] E} (hf : f.IsPositive) (h : A ≤ B) :
    LinearMap.trace ℂ E (f ∘ₗ A) ≤ LinearMap.trace ℂ E (f ∘ₗ B) := by
  rw [← sub_nonneg, ← map_sub, ← LinearMap.comp_sub]
  exact trace_comp_nonneg hf ((LinearMap.le_def A B).mp h)

end Factorization

end Qhl
