import Qhl.HSpace.Cast
import Qhl.Foundations.Basic

/-!
# Labelled Hilbert spaces: vector tensor

Mirror of the vector-tensor layer of `CoqQ/src/dirac/hstensor.v` (spec 02 §4,
subgoals H-10..H-14, milestone M2).

* `tenv D u v` (scoped notation `u ⊗ᵥ v`) — vector tensor (CoqQ `tenv`)
* `tenvBil D` — the tensor packaged as a bilinear map (H-10)
* `tenv_inner`, `tenv_norm`, `deltav_split`, `deltav_merge` (H-11)
* `tenv_conj` (H-12)
* `tenv_castA`/`tenv_castC`/`tenv_empty_right`/`tenv_empty_left` (H-13);
  all *unconditional* — no disjointness — and stated for an arbitrary proof of
  the label-set equality, so by proof irrelevance they apply to any such cast
* `tenvFamily D f u`, `tenvFamily_inner`, `tenvFamily_succ` (H-14)

The definitional payoff of Decision F1: `cdv_tenv` (CoqQ `cdvT`) is `rfl`, and
the cast laws are `funext` plus index computation (proof irrelevance makes all
composite restrictions of the same classical state definitionally equal).
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S T U W : Finset L}

/-! ## Index plumbing (additions to H-4 used by the cast laws) -/

namespace QIdx

/-- Restriction along `S ⊆ S` is the identity (by proof irrelevance). -/
@[simp, HS_simps]
theorem res_self (h : S ⊆ S) (k : QIdx D S) : res D h k = k := rfl

/-- A restriction absorbs a preceding cast (by proof irrelevance). -/
@[simp, HS_simps, cast_simps]
theorem res_cast (h₁ : S ⊆ T) (h₂ : U = T) (k : QIdx D U) :
    res D h₁ (cast D h₂ k) = res D (fun _ hi => h₂.symm ▸ h₁ hi) k := rfl

end QIdx

/-! ## The vector tensor (CoqQ `tenv`, `hstensor.v:946`) -/

/-- Vector tensor of labelled states: the coefficient at a classical state on
`S ∪ T` is the product of the coefficients at its restrictions. CoqQ `tenv`
(`hstensor.v:946`). Scoped notation: `u ⊗ᵥ v`. -/
noncomputable def tenv (u : HS D S) (v : HS D T) : HS D (S ∪ T) :=
  WithLp.toLp 2 fun k =>
    u (QIdx.res D subset_union_left k) * v (QIdx.res D subset_union_right k)

@[inherit_doc tenv]
scoped infixl:100 " ⊗ᵥ " => tenv _

@[simp, HS_simps]
theorem tenv_apply (u : HS D S) (v : HS D T) (k : QIdx D (S ∪ T)) :
    tenv D u v k =
      u (QIdx.res D subset_union_left k) * v (QIdx.res D subset_union_right k) :=
  rfl

/-- CoqQ `cdvT` (`hstensor.v:1123`); holds by `rfl` (Decision F1 payoff). -/
@[simp, HS_simps]
theorem cdv_tenv (k : QIdx D (S ∪ T)) (u : HS D S) (v : HS D T) :
    cdv D k (tenv D u v) =
      cdv D (QIdx.res D subset_union_left k) u *
        cdv D (QIdx.res D subset_union_right k) v :=
  rfl

/-! ## H-10: bilinearity (CoqQ bilinear instances, `hstensor.v:1044-1099`) -/

theorem tenv_add_left (u₁ u₂ : HS D S) (v : HS D T) :
    tenv D (u₁ + u₂) v = tenv D u₁ v + tenv D u₂ v := by
  refine PiLp.ext fun k => ?_
  simp only [tenv_apply, PiLp.add_apply, add_mul]

theorem tenv_add_right (u : HS D S) (v₁ v₂ : HS D T) :
    tenv D u (v₁ + v₂) = tenv D u v₁ + tenv D u v₂ := by
  refine PiLp.ext fun k => ?_
  simp only [tenv_apply, PiLp.add_apply, mul_add]

theorem tenv_smul_left (c : ℂ) (u : HS D S) (v : HS D T) :
    tenv D (c • u) v = c • tenv D u v := by
  refine PiLp.ext fun k => ?_
  simp only [tenv_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem tenv_smul_right (c : ℂ) (u : HS D S) (v : HS D T) :
    tenv D u (c • v) = c • tenv D u v := by
  refine PiLp.ext fun k => ?_
  simp only [tenv_apply, PiLp.smul_apply, smul_eq_mul]
  ring

@[simp]
theorem tenv_zero_left (v : HS D T) : tenv D (0 : HS D S) v = 0 := by
  refine PiLp.ext fun k => ?_
  simp only [tenv_apply, PiLp.zero_apply, zero_mul]

@[simp]
theorem tenv_zero_right (u : HS D S) : tenv D u (0 : HS D T) = 0 := by
  refine PiLp.ext fun k => ?_
  simp only [tenv_apply, PiLp.zero_apply, mul_zero]

/-- The vector tensor as a bilinear map. CoqQ bilinear-morphism instances
(`hstensor.v:1044-1099`). -/
noncomputable def tenvBil : HS D S →ₗ[ℂ] HS D T →ₗ[ℂ] HS D (S ∪ T) :=
  LinearMap.mk₂ ℂ (tenv D) (tenv_add_left D) (tenv_smul_left D)
    (tenv_add_right D) (tenv_smul_right D)

@[simp]
theorem tenvBil_apply (u : HS D S) (v : HS D T) : tenvBil D u v = tenv D u v := rfl

/-! ## H-11: inner products, norm, and basis behavior -/

/-- CoqQ `tenv_dot` (`hstensor.v:1101`): on a *disjoint* union the tensor
multiplies inner products. -/
theorem tenv_inner (hd : Disjoint S T) (u₁ u₂ : HS D S) (v₁ v₂ : HS D T) :
    ⟪tenv D u₁ v₁, tenv D u₂ v₂⟫ = ⟪u₁, u₂⟫ * ⟪v₁, v₂⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  rw [Fintype.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (splitEquiv D hd) _ _ fun k => ?_
  simp only [splitEquiv_apply, tenv_apply, map_mul]
  ring

/-- CoqQ `tenv_norm` (`hstensor.v:1110`). -/
theorem tenv_norm (hd : Disjoint S T) (u : HS D S) (v : HS D T) :
    ‖tenv D u v‖ = ‖u‖ * ‖v‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), tenv_inner D hd, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K, ← mul_pow, ← RCLike.ofReal_mul, ← RCLike.ofReal_pow,
    RCLike.ofReal_re, Real.sqrt_sq (mul_nonneg (norm_nonneg u) (norm_nonneg v))]

/-- CoqQ `dv_split` (`hstensor.v:1151`): a basis ket on a union splits as a
tensor of basis kets — *unconditionally*. -/
theorem deltav_split (k : QIdx D (S ∪ T)) :
    deltav D k = tenv D (deltav D (QIdx.res D subset_union_left k))
      (deltav D (QIdx.res D subset_union_right k)) := by
  refine PiLp.ext fun l => ?_
  have hlk : l = k ↔
      QIdx.res D subset_union_left l = QIdx.res D subset_union_left k ∧
        QIdx.res D subset_union_right l = QIdx.res D subset_union_right k := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h₁, h₂⟩
      funext i
      rcases mem_union.1 i.2 with hi | hi
      · exact congrFun h₁ ⟨i, hi⟩
      · exact congrFun h₂ ⟨i, hi⟩
  simp only [tenv_apply, deltav_apply, hlk]
  by_cases h₁ : QIdx.res D subset_union_left l = QIdx.res D subset_union_left k <;>
    by_cases h₂ : QIdx.res D subset_union_right l = QIdx.res D subset_union_right k <;>
      simp [h₁, h₂]

/-- CoqQ `dv_tensor` (`hstensor.v:1155`): a tensor of basis kets is the basis
ket at the merged classical state (needs disjointness). -/
theorem deltav_merge (hd : Disjoint S T) (k : QIdx D S) (l : QIdx D T) :
    tenv D (deltav D k) (deltav D l) = deltav D (QIdx.merge D k l) := by
  refine PiLp.ext fun m => ?_
  have hm : m = QIdx.merge D k l ↔
      QIdx.res D subset_union_left m = k ∧ QIdx.res D subset_union_right m = l := by
    constructor
    · rintro rfl
      exact ⟨QIdx.res_merge_left D subset_union_left k l,
        QIdx.res_merge_right D hd subset_union_right k l⟩
    · rintro ⟨h₁, h₂⟩
      conv_lhs => rw [← QIdx.merge_res D subset_union_left subset_union_right m]
      rw [h₁, h₂]
  simp only [tenv_apply, deltav_apply, hm]
  by_cases h₁ : QIdx.res D subset_union_left m = k <;>
    by_cases h₂ : QIdx.res D subset_union_right m = l <;> simp [h₁, h₂]

/-! ## H-12: conjugation -/

/-- CoqQ `tenv_conj` (`hstensor.v:1173`). -/
@[simp]
theorem tenv_conj (u : HS D S) (v : HS D T) :
    conjV (tenv D u v) = tenv D (conjV u) (conjV v) := by
  refine PiLp.ext fun k => ?_
  simp only [conjV_apply, tenv_apply, star_mul']

/-! ## H-13: cast laws — associativity, commutativity, unit

All unconditional, and stated for an arbitrary proof `h` of the label-set
equality (proof irrelevance), so `simp` matches any cast of that shape. -/

/-- CoqQ `tenv_castA` (`hstensor.v:1182`): associativity up to cast. -/
@[simp, cast_simps]
theorem tenv_castA (h : S ∪ (T ∪ W) = (S ∪ T) ∪ W) (u : HS D S) (v : HS D T)
    (w : HS D W) :
    castH D h (tenv D u (tenv D v w)) = tenv D (tenv D u v) w := by
  refine PiLp.ext fun m => ?_
  simp only [castH_apply, tenv_apply, QIdx.res_cast, QIdx.res_res]
  ring

/-- CoqQ `tenv_castC` (`hstensor.v:1191`): commutativity up to cast. -/
@[simp, cast_simps]
theorem tenv_castC (h : S ∪ T = T ∪ S) (u : HS D S) (v : HS D T) :
    castH D h (tenv D u v) = tenv D v u := by
  refine PiLp.ext fun m => ?_
  simp only [castH_apply, tenv_apply, QIdx.res_cast]
  ring

/-- CoqQ `tenv_idx0r` (`hstensor.v:1200`): the empty-register basis ket is a
right unit up to cast. -/
@[simp, cast_simps]
theorem tenv_empty_right (h : S ∪ ∅ = S) (u : HS D S) :
    castH D h (tenv D u (deltav D (default : QIdx D ∅))) = u := by
  refine PiLp.ext fun m => ?_
  have h0 : ∀ l : QIdx D ∅, deltav D (default : QIdx D ∅) l = 1 := fun l => by
    rw [deltav_apply, if_pos (Subsingleton.elim l default)]
  simp only [castH_apply, tenv_apply, QIdx.res_cast, QIdx.res_self, h0, mul_one]

/-- The `∅`-on-the-left version of `tenv_empty_right`. -/
@[simp, cast_simps]
theorem tenv_empty_left (h : ∅ ∪ S = S) (u : HS D S) :
    castH D h (tenv D (deltav D (default : QIdx D ∅)) u) = u := by
  refine PiLp.ext fun m => ?_
  have h0 : ∀ l : QIdx D ∅, deltav D (default : QIdx D ∅) l = 1 := fun l => by
    rw [deltav_apply, if_pos (Subsingleton.elim l default)]
  simp only [castH_apply, tenv_apply, QIdx.res_cast, QIdx.res_self, h0, one_mul]

/-! ## H-14: the family tensor (CoqQ `tenvm`, `hstensor.v:950`) -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Finset L)

/-- Tensor of a finite family of labelled states. CoqQ `tenvm`
(`hstensor.v:950`). -/
noncomputable def tenvFamily (u : ∀ j, HS D (f j)) : HS D (univ.biUnion f) :=
  WithLp.toLp 2 fun k =>
    ∏ j, u j (QIdx.res D (subset_biUnion_of_mem f (mem_univ j)) k)

@[simp, HS_simps]
theorem tenvFamily_apply (u : ∀ j, HS D (f j)) (k : QIdx D (univ.biUnion f)) :
    tenvFamily D f u k =
      ∏ j, u j (QIdx.res D (subset_biUnion_of_mem f (mem_univ j)) k) :=
  rfl

/-- CoqQ `tenvm_dot` (`hstensor.v:1237`): on a pairwise-disjoint family the
family tensor multiplies inner products. -/
theorem tenvFamily_inner (hd : Pairwise (Function.onFun Disjoint f))
    (u v : ∀ j, HS D (f j)) :
    ⟪tenvFamily D f u, tenvFamily D f v⟫ = ∏ j, ⟪u j, v j⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Fintype.sum_equiv (packEquiv D f hd) _ _ fun k => ?_
  simp only [packEquiv_apply, tenvFamily_apply, map_prod, ← Finset.prod_mul_distrib]

/-- CoqQ `tenvm_recl` (`hstensor.v:1274`): the family tensor peels off its head
factor, up to cast — *unconditionally*. -/
theorem tenvFamily_succ {n : ℕ} (f : Fin (n + 1) → Finset L) (u : ∀ j, HS D (f j))
    (h : f 0 ∪ univ.biUnion (fun j : Fin n => f j.succ) = univ.biUnion f) :
    castH D h
      (tenv D (u 0) (tenvFamily D (fun j : Fin n => f j.succ) fun j => u j.succ)) =
      tenvFamily D f u := by
  refine PiLp.ext fun k => ?_
  simp only [castH_apply, tenv_apply, tenvFamily_apply, QIdx.res_cast, QIdx.res_res,
    Fin.prod_univ_succ]

/-- The family tensor over an empty index type is the empty-register basis ket,
up to cast (base case of CoqQ `tenvm_correct`, `dirac.v:2156`). -/
theorem tenvFamily_isEmpty [IsEmpty ι] (u : ∀ j, HS D (f j))
    (h : (∅ : Finset L) = univ.biUnion f) :
    tenvFamily D f u = castH D h (deltav D (default : QIdx D ∅)) := by
  have : Subsingleton (QIdx D (univ.biUnion f)) :=
    h ▸ inferInstanceAs (Subsingleton (QIdx D ∅))
  refine PiLp.ext fun k => ?_
  simp only [tenvFamily_apply, univ_eq_empty, prod_empty, castH_deltav, deltav_apply]
  rw [if_pos (Subsingleton.elim _ _)]

/-- Reindexing the family tensor along an equivalence of index types only casts
it (CoqQ handles this inside `tenvm_correct` via `\big`-reindexing,
`dirac.v:2156`). -/
theorem tenvFamily_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι)
    (u : ∀ j, HS D (f j)) (h : univ.biUnion f = univ.biUnion fun j => f (e j)) :
    tenvFamily D (fun j => f (e j)) (fun j => u (e j)) =
      castH D h (tenvFamily D f u) := by
  refine PiLp.ext fun k => ?_
  simp only [tenvFamily_apply, castH_apply, QIdx.res_cast]
  exact Fintype.prod_equiv e _ _ fun j => rfl

end Qhl
