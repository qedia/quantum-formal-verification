import Mathlib.Analysis.InnerProductSpace.PiL2
import Qhl.Tactic.Attr

/-!
# Labelled Hilbert spaces: carrier and canonical basis

Mirror of the carrier/basis layer of `CoqQ/src/dirac/hstensor.v` (spec 02 §1,
milestone M0 of spec 05).

Fixtures (Decision F1, spec 01): labels `L`, classical-state types `D i`; the
labelled space on `S : Finset L` is `EuclideanSpace ℂ` over the classical
states `QIdx D S`, so all Hilbert-space structure is inherited from mathlib.

* `QIdx D S` — classical states on `S` (CoqQ `'Idx[H]_S`)
* `HS D S` — the labelled Hilbert space (CoqQ `'H[H]_S`)
* `LinM D S T`, `EndM D S` — labelled linear maps (CoqQ `'F[H]_(S,T)`, `'F[H]_S`)
* `deltav D k` — canonical basis ket (CoqQ `deltav`)
* `cdv D k u` — coefficient at a classical state (CoqQ `cdv`)
* `emptyIso D` — `HS D ∅ ≃ₗᵢ[ℂ] ℂ` (CoqQ `sv2s`/`s2sv`)
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]

/-- Classical states of the register set `S` — the canonical basis index of
`HS D S`. CoqQ: `'Idx[H]_S` (`hstensor.v`). -/
abbrev QIdx (S : Finset L) : Type _ := ∀ i : ↥S, D i

/-- The labelled Hilbert space on the label set `S`, concretely `EuclideanSpace`
over classical states (Decision F1). CoqQ: `'H[H]_S`. -/
abbrev HS (S : Finset L) : Type _ := EuclideanSpace ℂ (QIdx D S)

/-- Labelled linear maps. CoqQ: `'F[H]_(S,T)`. -/
abbrev LinM (S T : Finset L) : Type _ := HS D S →ₗ[ℂ] HS D T

/-- Labelled endomorphisms. CoqQ: `'F[H]_S`. -/
abbrev EndM (S : Finset L) : Type _ := LinM D S S

variable {S T : Finset L}

/-! ## H-1: cardinality and dimension -/

/-- CoqQ `card_idx` (`hstensor.v:150`). -/
theorem card_qIdx (S : Finset L) :
    Fintype.card (QIdx D S) = ∏ i ∈ S, Fintype.card (D i) := by
  rw [Fintype.card_pi]
  exact S.prod_coe_sort fun i => Fintype.card (D i)

/-- CoqQ `dim_setten` (`hstensor.v:285`). -/
theorem finrank_HS (S : Finset L) :
    Module.finrank ℂ (HS D S) = ∏ i ∈ S, Fintype.card (D i) := by
  rw [finrank_euclideanSpace, card_qIdx]

/-! ## H-2: the canonical basis `deltav` and coefficients `cdv` -/

/-- Canonical basis ket at classical state `k`. CoqQ: `deltav`. -/
noncomputable def deltav (k : QIdx D S) : HS D S := EuclideanSpace.single k 1

/-- Coefficient of `u` at classical state `k`. CoqQ: `cdv`. -/
def cdv (k : QIdx D S) (u : HS D S) : ℂ := u k

theorem deltav_def (k : QIdx D S) : deltav D k = EuclideanSpace.single k 1 := rfl

@[simp, HS_simps]
theorem cdv_apply (k : QIdx D S) (u : HS D S) : cdv D k u = u k := rfl

@[simp, HS_simps]
theorem deltav_apply (k l : QIdx D S) :
    deltav D k l = if l = k then 1 else 0 := by
  simp [deltav]

/-- CoqQ `dv_dot` (`hstensor.v:214`): `deltav` is an orthonormal family. -/
theorem dv_dot (k l : QIdx D S) :
    ⟪deltav D k, deltav D l⟫ = if k = l then 1 else 0 := by
  simp [deltav, EuclideanSpace.inner_single_left]

/-- CoqQ `dec_dv` (`hstensor.v:238`): expansion in the canonical basis. -/
theorem dec_dv (u : HS D S) : u = ∑ k, cdv D k u • deltav D k := by
  simpa [deltav, cdv, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
    ((EuclideanSpace.basisFun (QIdx D S) ℂ).sum_repr u).symm

/-- CoqQ `dot_cdv` (`hstensor.v:252`): inner product via coefficients. -/
theorem dot_cdv (u v : HS D S) :
    ⟪u, v⟫ = ∑ k, star (cdv D k u) * cdv D k v := by
  simp [PiLp.inner_apply, RCLike.inner_apply, RCLike.star_def, mul_comm]

/-- The coordinates of the value of a linear map, from the coordinates of its
argument: expand the argument in the canonical basis. -/
theorem apply_eq_sum_cdv (f : LinM D S T) (u : HS D S) (l : QIdx D T) :
    f u l = ∑ m, u m * f (deltav D m) l := by
  conv_lhs => rw [dec_dv D u]
  rw [map_sum]
  simp [smul_eq_mul]

/-- CoqQ `cdvP` (`hstensor.v:279`): vectors with equal coefficients are equal. -/
theorem cdvP {u v : HS D S} (h : ∀ k, cdv D k u = cdv D k v) : u = v :=
  PiLp.ext h

/-- CoqQ `lfunPD` (`hstensor.v:457`): linear maps agreeing on `deltav` are equal. -/
theorem linM_ext {f g : LinM D S T} (h : ∀ k, f (deltav D k) = g (deltav D k)) :
    f = g :=
  (EuclideanSpace.basisFun (QIdx D S) ℂ).toBasis.ext fun k => by
    simpa only [deltav, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply] using h k

/-! ## H-6: the empty register -/

/-- CoqQ `idx0E`/`dim_set0` (`hstensor.v:759,753`): the empty register has a
unique classical state. (Via `Finset.instIsEmpty` and `Pi.uniqueOfIsEmpty`;
recorded here as the H-6 acceptance check.) -/
example : Unique (QIdx D ∅) := Pi.uniqueOfIsEmpty _

/-- `HS D ∅` is canonically `ℂ`. CoqQ: `sv2s`/`s2sv` (`hstensor.v:1364-1493`). -/
def emptyIso : HS D ∅ ≃ₗᵢ[ℂ] ℂ where
  toLinearEquiv :=
    { toFun := fun u => u default
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun c => WithLp.toLp 2 fun _ => c
      left_inv := fun u => by
        ext k
        exact congrArg u.ofLp (Subsingleton.elim default k)
      right_inv := fun _ => rfl }
  norm_map' := fun u => by
    change ‖u default‖ = ‖u‖
    rw [EuclideanSpace.norm_eq, Fintype.sum_unique]
    exact (Real.sqrt_sq (norm_nonneg (u default))).symm

@[simp, HS_simps]
theorem emptyIso_apply (u : HS D ∅) : emptyIso D u = u default := rfl

@[simp, HS_simps]
theorem emptyIso_symm_apply (c : ℂ) (k : QIdx D ∅) :
    (emptyIso D).symm c k = c := rfl

end Qhl
