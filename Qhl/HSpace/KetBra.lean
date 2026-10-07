import Qhl.HSpace.Basic
import Qhl.Foundations.Basic

/-!
# Kets, bras and scalars as labelled linear maps

Mirror of `CoqQ/src/dirac/hstensor.v:1364-1493` (spec 02 §5, subgoal H-15).

`HS D ∅` is one-dimensional with canonical unit vector `deltav D default`
(and `⟪deltav D default, w⟫ = emptyIso D w`), so kets, bras and scalars embed
into the labelled linear maps consumed by the Dirac layer (spec 03):

* `toKetM D v` / `ofKetM D f` — the ket `|v⟩` as an `(∅,S)`-block map and back
  (CoqQ `v2f`/`f2v`), bundled as `toKetLM D : HS D S ≃ₗ[ℂ] LinM D ∅ S`
* `toBraM D v` / `ofBraM D f` — the bra `⟨v|` as an `(S,∅)`-block map and back
  (CoqQ `v2df`/`df2v`, conjugate-linear)
* `toScalarM D c` — a scalar as an `(∅,∅)`-block map (CoqQ `s2sf`)
* H-15: round trips, (anti)linearity, adjoints (`(toKetM D v)† = toBraM D v`),
  `comp_dot` (`⟨u| ∘ |v⟩ = ⟪u,v⟫`), `comp_out` (`|v⟩ ∘ ⟨u| = outerLM v u`),
  and the `toScalarM` algebra (ring-hom laws, adjoint, injectivity, trace).
-/

namespace Qhl

open scoped ComplexInnerProductSpace

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S : Finset L}

/-- `⟪deltav D k, ·⟫` extracts the coefficient at `k` (spec 02 §5 header; at
`k = default` this is `⟪deltav D default, w⟫ = emptyIso D w`, definitionally). -/
@[simp, HS_simps]
theorem inner_deltav (k : QIdx D S) (w : HS D S) : ⟪deltav D k, w⟫ = w k := by
  simp [deltav, EuclideanSpace.inner_single_left]

/-- `|δ∅⟩⟨δ∅|` is the identity of the one-dimensional space `HS D ∅`. -/
@[simp]
theorem outerLM_deltav_default :
    outerLM (deltav D (default : QIdx D ∅)) (deltav D (default : QIdx D ∅))
      = (1 : LinM D ∅ ∅) :=
  linM_ext D fun k => by
    rw [Subsingleton.elim k default, outerLM_apply, dv_dot]
    simp

/-! ## The five definitions (CoqQ `hstensor.v:1364-1493`) -/

/-- The ket `|v⟩` as the `(∅,S)`-block map `|v⟩⟨δ∅|`. CoqQ: `v2f`. -/
noncomputable def toKetM (v : HS D S) : LinM D ∅ S :=
  outerLM v (deltav D (default : QIdx D ∅))

/-- The bra `⟨v|` as the `(S,∅)`-block map `|δ∅⟩⟨v|`. CoqQ: `v2df`. -/
noncomputable def toBraM (v : HS D S) : LinM D S ∅ :=
  outerLM (deltav D (default : QIdx D ∅)) v

/-- Recover a ket from its `(∅,S)`-block map. CoqQ: `f2v`. -/
noncomputable def ofKetM (f : LinM D ∅ S) : HS D S :=
  f (deltav D default)

/-- Recover a ket from its bra `(S,∅)`-block map (conjugate-linear in `f`).
CoqQ: `df2v`. -/
noncomputable def ofBraM (f : LinM D S ∅) : HS D S :=
  LinearMap.adjoint f (deltav D default)

/-- A scalar as the `(∅,∅)`-block map `c • 1`. CoqQ: `s2sf`. -/
def toScalarM (c : ℂ) : LinM D ∅ ∅ := c • 1

theorem toKetM_def (v : HS D S) :
    toKetM D v = outerLM v (deltav D (default : QIdx D ∅)) := rfl

theorem toBraM_def (v : HS D S) :
    toBraM D v = outerLM (deltav D (default : QIdx D ∅)) v := rfl

theorem ofKetM_def (f : LinM D ∅ S) : ofKetM D f = f (deltav D default) := rfl

theorem ofBraM_def (f : LinM D S ∅) :
    ofBraM D f = LinearMap.adjoint f (deltav D default) := rfl

theorem toScalarM_def (c : ℂ) : toScalarM D c = c • 1 := rfl

/-! ## Apply lemmas -/

/-- `toKetM D v` sends `w : HS D ∅` to `emptyIso D w • v` (the alternative
definition of spec 02 §5, with `emptyIso D w = w default` by `rfl`). -/
@[simp, HS_simps]
theorem toKetM_apply (v : HS D S) (w : HS D ∅) :
    toKetM D v w = w default • v := by
  simp [toKetM_def]

@[simp, HS_simps]
theorem toBraM_apply (v w : HS D S) :
    toBraM D v w = ⟪v, w⟫ • deltav D default := rfl

@[simp, HS_simps]
theorem toScalarM_apply (c : ℂ) (w : HS D ∅) : toScalarM D c w = c • w := rfl

/-! ## Adjoints (H-15): `(|v⟩)† = ⟨v|` -/

@[simp]
theorem adjoint_toKetM (v : HS D S) :
    LinearMap.adjoint (toKetM D v) = toBraM D v :=
  adjoint_outerLM v (deltav D default)

@[simp]
theorem adjoint_toBraM (v : HS D S) :
    LinearMap.adjoint (toBraM D v) = toKetM D v :=
  adjoint_outerLM (deltav D default) v

/-! ## Round trips (H-15) -/

@[simp]
theorem ofKetM_toKetM (v : HS D S) : ofKetM D (toKetM D v) = v := by
  simp [ofKetM_def]

@[simp]
theorem toKetM_ofKetM (f : LinM D ∅ S) : toKetM D (ofKetM D f) = f :=
  linM_ext D fun k => by
    rw [Subsingleton.elim k default]
    simp [ofKetM_def]

@[simp]
theorem ofBraM_toBraM (v : HS D S) : ofBraM D (toBraM D v) = v := by
  simp [ofBraM_def]

@[simp]
theorem toBraM_ofBraM (f : LinM D S ∅) : toBraM D (ofBraM D f) = f := by
  have h := congrArg LinearMap.adjoint (toKetM_ofKetM D (LinearMap.adjoint f))
  rw [adjoint_toKetM, LinearMap.adjoint_adjoint] at h
  exact h

/-! ## (Anti)linearity (H-15) -/

theorem toKetM_add (u v : HS D S) :
    toKetM D (u + v) = toKetM D u + toKetM D v :=
  outerLM_add_left u v (deltav D default)

theorem toKetM_smul (c : ℂ) (v : HS D S) :
    toKetM D (c • v) = c • toKetM D v :=
  outerLM_smul_left c v (deltav D default)

theorem ofKetM_add (f g : LinM D ∅ S) :
    ofKetM D (f + g) = ofKetM D f + ofKetM D g := rfl

theorem ofKetM_smul (c : ℂ) (f : LinM D ∅ S) :
    ofKetM D (c • f) = c • ofKetM D f := rfl

theorem toBraM_add (u v : HS D S) :
    toBraM D (u + v) = toBraM D u + toBraM D v :=
  outerLM_add_right (deltav D default) u v

theorem toBraM_smul (c : ℂ) (v : HS D S) :
    toBraM D (c • v) = star c • toBraM D v :=
  outerLM_smul_right c (deltav D default) v

theorem ofBraM_add (f g : LinM D S ∅) :
    ofBraM D (f + g) = ofBraM D f + ofBraM D g := by
  simp [ofBraM_def]

theorem ofBraM_smul (c : ℂ) (f : LinM D S ∅) :
    ofBraM D (c • f) = star c • ofBraM D f := by
  simp [ofBraM_def, map_smulₛₗ, RCLike.star_def]

/-- `toKetM` bundled: kets are linearly equivalent to their `(∅,S)`-block maps. -/
noncomputable def toKetLM : HS D S ≃ₗ[ℂ] LinM D ∅ S where
  toFun := toKetM D
  map_add' := toKetM_add D
  map_smul' := toKetM_smul D
  invFun := ofKetM D
  left_inv := ofKetM_toKetM D
  right_inv := toKetM_ofKetM D

@[simp]
theorem toKetLM_apply (v : HS D S) : toKetLM D v = toKetM D v := rfl

@[simp]
theorem toKetLM_symm_apply (f : LinM D ∅ S) :
    (toKetLM D).symm f = ofKetM D f := rfl

/-! ## Composition: inner and outer products -/

/-- CoqQ `comp_dot` (`hstensor.v:1486`): `⟨u| ∘ |v⟩ = ⟪u, v⟫` as scalar maps. -/
theorem comp_dot (u v : HS D S) :
    toBraM D u ∘ₗ toKetM D v = toScalarM D ⟪u, v⟫ := by
  rw [toBraM_def, toKetM_def, outerLM_comp, outerLM_deltav_default D]
  rfl

/-- CoqQ `comp_out` (`hstensor.v:1493`): `|v⟩ ∘ ⟨u| = |v⟩⟨u|`. -/
theorem comp_out (u v : HS D S) :
    toKetM D v ∘ₗ toBraM D u = outerLM v u := by
  rw [toKetM_def, toBraM_def, outerLM_comp, dv_dot]
  simp

/-- Postcomposition acts on the ket: `f ∘ |v⟩ = |f v⟩` (CoqQ uses this inline;
cf. `lind_ketG`, `dirac.v:1884`). -/
theorem comp_toKetM {T : Finset L} (f : LinM D S T) (v : HS D S) :
    f ∘ₗ toKetM D v = toKetM D (f v) :=
  LinearMap.ext fun w => by simp

/-! ## `toScalarM` algebra (H-15) -/

@[simp]
theorem toScalarM_zero : toScalarM D 0 = 0 := zero_smul ℂ (1 : LinM D ∅ ∅)

@[simp]
theorem toScalarM_one : toScalarM D 1 = 1 := one_smul ℂ (1 : LinM D ∅ ∅)

theorem toScalarM_add (c c' : ℂ) :
    toScalarM D (c + c') = toScalarM D c + toScalarM D c' :=
  add_smul c c' (1 : LinM D ∅ ∅)

theorem toScalarM_mul (c c' : ℂ) :
    toScalarM D (c * c') = toScalarM D c ∘ₗ toScalarM D c' :=
  LinearMap.ext fun w => mul_smul c c' w

@[simp]
theorem adjoint_toScalarM (c : ℂ) :
    LinearMap.adjoint (toScalarM D c) = toScalarM D (star c) := by
  refine ((LinearMap.eq_adjoint_iff _ _).mpr fun x y => ?_).symm
  simp [inner_smul_left, inner_smul_right, RCLike.star_def]

theorem toScalarM_injective : Function.Injective (toScalarM D) := fun c c' h => by
  simpa using congrArg (fun f : LinM D ∅ ∅ => f (deltav D default) default) h

@[simp]
theorem trace_toScalarM (c : ℂ) :
    LinearMap.trace ℂ (HS D ∅) (toScalarM D c) = c := by
  rw [toScalarM_def, map_smul, LinearMap.trace_one, finrank_HS]
  simp

end Qhl
