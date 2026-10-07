import Mathlib.Analysis.InnerProductSpace.Adjoint
import Qhl.HSpace.Index

/-!
# Labelled Hilbert spaces: casts of vectors and operators

Mirror of the cast layer of `CoqQ/src/dirac/hstensor.v` (spec 02 §3,
subgoal H-9). Decision H1: casts are *reindexing isometries* built from
`QIdx.cast`, never `Eq.rec` on the space.

* `castH D h : HS D S ≃ₗᵢ[ℂ] HS D T` for `h : S = T` (CoqQ `casths`)
* `castF D h₁ h₂ : LinM D S T ≃ₗ[ℂ] LinM D S' T'` (CoqQ `castlf`)

Componentwise normal forms (the `cast_simps` simp set rewrites to these):

* `castH_apply : castH D h u l = u (QIdx.cast D h.symm l)`
* `castF_apply : castF D h₁ h₂ f u = castH D h₂ (f (castH D h₁.symm u))`

`castH_rfl`/`castF_rfl` are stated for arbitrary self-equality proofs, so by
proof irrelevance they also collapse the `h.trans h.symm`-style casts produced
by `castH_castH`.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S T U S' T' U' : Finset L}

/-- Cast of vectors along an equality of label sets, as the reindexing isometry
along `QIdx.cast D h` (Decision H1). CoqQ `casths` (`hstensor.v:312`). -/
noncomputable def castH (h : S = T) : HS D S ≃ₗᵢ[ℂ] HS D T :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (QIdx.cast D h)

/-! ## H-9: the `cast_simps` suite for `castH` -/

/-- Componentwise normal form of `castH`. -/
@[simp, cast_simps]
theorem castH_apply (h : S = T) (u : HS D S) (l : QIdx D T) :
    castH D h u l = u (QIdx.cast D h.symm l) :=
  rfl

/-- CoqQ `casths_id` (`hstensor.v:312-363`). -/
@[simp, cast_simps]
theorem castH_rfl (h : S = S) : castH D h = LinearIsometryEquiv.refl ℂ (HS D S) :=
  LinearIsometryEquiv.ext fun _ => rfl

/-- CoqQ `casths_comp` (`hstensor.v:312-363`). -/
@[simp, cast_simps]
theorem castH_trans (h₁ : S = T) (h₂ : T = U) :
    (castH D h₁).trans (castH D h₂) = castH D (h₁.trans h₂) :=
  LinearIsometryEquiv.ext fun _ => rfl

/-- Applied form of `castH_trans`: consecutive casts collapse. -/
@[simp, cast_simps]
theorem castH_castH (h₁ : S = T) (h₂ : T = U) (u : HS D S) :
    castH D h₂ (castH D h₁ u) = castH D (h₁.trans h₂) u :=
  rfl

/-- CoqQ `casths_symm` (`hstensor.v:312-363`). -/
@[simp, cast_simps]
theorem castH_symm (h : S = T) : (castH D h).symm = castH D h.symm :=
  LinearIsometryEquiv.ext fun _ => rfl

/-- CoqQ `deltav_cast` (`hstensor.v:340`). -/
@[simp, cast_simps]
theorem castH_deltav (h : S = T) (k : QIdx D S) :
    castH D h (deltav D k) = deltav D (QIdx.cast D h k) := by
  subst h; simp

/-- `castH` preserves inner products (free: it is an isometry). -/
@[simp, cast_simps]
theorem castH_inner (h : S = T) (u v : HS D S) :
    ⟪castH D h u, castH D h v⟫ = ⟪u, v⟫ :=
  (castH D h).inner_map_map u v

/-! ## H-9: casts of operators -/

/-- Cast of operators: conjugation by `castH` packaged as a linear equivalence.
CoqQ `castlf` (`hstensor.v:364`). -/
noncomputable def castF (h₁ : S = S') (h₂ : T = T') : LinM D S T ≃ₗ[ℂ] LinM D S' T' :=
  (castH D h₁).toLinearEquiv.arrowCongr (castH D h₂).toLinearEquiv

/-- Normal form of `castF`: conjugation by `castH`. -/
@[simp, cast_simps]
theorem castF_apply (h₁ : S = S') (h₂ : T = T') (f : LinM D S T) (u : HS D S') :
    castF D h₁ h₂ f u = castH D h₂ (f (castH D h₁.symm u)) :=
  rfl

/-- CoqQ `castlf_id` (`hstensor.v:364-456`). -/
@[simp, cast_simps]
theorem castF_rfl (h₁ : S = S) (h₂ : T = T) :
    castF D h₁ h₂ = LinearEquiv.refl ℂ (LinM D S T) :=
  LinearEquiv.ext fun _ => LinearMap.ext fun _ => rfl

/-- CoqQ `castlf_comp` (`hstensor.v:378`). -/
@[simp, cast_simps]
theorem castF_comp (h₁ : S = S') (h₂ : T = T') (h₃ : U = U') (g : LinM D T U)
    (f : LinM D S T) :
    castF D h₁ h₃ (g ∘ₗ f) = castF D h₂ h₃ g ∘ₗ castF D h₁ h₂ f :=
  LinearMap.ext fun _ => rfl

/-- CoqQ `castlf_adj` (`hstensor.v:434`). -/
@[simp, cast_simps]
theorem castF_adj (h₁ : S = S') (h₂ : T = T') (f : LinM D S T) :
    LinearMap.adjoint (castF D h₁ h₂ f) = castF D h₂ h₁ (LinearMap.adjoint f) := by
  subst h₁; subst h₂; simp

/-- CoqQ `castlf1` (`hstensor.v:446`). -/
@[simp, cast_simps]
theorem castF_one (h : S = T) : castF D h h (1 : EndM D S) = 1 := by
  subst h; simp

/-- Acceptance check (spec 05, M1): a `castH_trans`-style goal closes by
`simp [cast_simps]`. -/
example (h₁ : S = T) (h₂ : T = U) (u : HS D S) :
    castH D h₂ (castH D h₁ u) = castH D (h₁.trans h₂) u := by
  simp [cast_simps]

end Qhl
