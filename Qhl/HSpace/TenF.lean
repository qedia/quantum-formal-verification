import Qhl.HSpace.TenV

/-!
# Labelled Hilbert spaces: operator tensor

Mirror of the operator-tensor layer of `CoqQ/src/dirac/hstensor.v` (spec 02 §6,
subgoals H-16, H-17, H-19, milestone M3).

* `tenf D f g` (scoped notation `f ⊗ᶠ g`) — operator tensor, defined by
  `Basis.constr` on the `deltav` basis (CoqQ `ten_lfun`, `hstensor.v:1319`)
* `tenf_deltav`, bilinearity, `tenf_outerLM`, `tenf_apply`, interchange
  `tenf_comp`, `adjoint_tenf`/`conjLM_tenf`/`transposeLM_tenf`,
  `tenf_one_one` (H-16)
* `tenf_castA`/`tenf_castC`/`tenf_cast1r` (H-17), stated for arbitrary proofs
  of the label-set equalities like the `tenv` cast laws
* `tenfFamily D φ` with `tenfFamily_deltav`, `tenfFamily_apply`,
  `adjoint_tenfFamily`/`conjLM_tenfFamily`/`transposeLM_tenfFamily` (H-19,
  CoqQ `tenfm`, `hstensor.v:955`)

Side conditions: only `tenf_apply`/`tenf_comp`/`tenfFamily_apply` need
disjointness (of the *domain* label sets, resp. the middle sets for the
interchange law); everything else — including `tenf_outerLM`, the A/C/T
distribution laws and `tenf_one_one` — is unconditional, because matrix
entries of `tenf f g` factor through restrictions without any disjointness.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S T S₁ S₂ S₃ T₁ T₂ T₃ U₁ U₂ : Finset L}

/-! ## Helper lemmas on existing definitions -/

/-- Componentwise evaluation of a finite sum in `HS D S`. -/
@[simp, HS_simps]
theorem HS_sum_apply {α : Type*} (s : Finset α) (v : α → HS D S) (k : QIdx D S) :
    (∑ a ∈ s, v a) k = ∑ a ∈ s, v a k := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => simp [Finset.sum_cons, ih]

/-- `⟪w, deltav D k⟫` is the conjugated coefficient of `w` at `k`. -/
theorem inner_deltav_right (w : HS D S) (k : QIdx D S) :
    ⟪w, deltav D k⟫ = star (w k) := by
  rw [deltav_def, EuclideanSpace.inner_single_right, one_mul, RCLike.star_def]

/-- The canonical basis kets are fixed by componentwise conjugation. -/
@[simp, HS_simps]
theorem conjV_deltav (k : QIdx D S) : conjV (deltav D k) = deltav D k := by
  rw [deltav_def, conjV_single, star_one]

/-- Matrix entries of the adjoint are the conjugate-transposed entries. -/
theorem adjoint_deltav_apply (h : LinM D S T) (l : QIdx D T) (k : QIdx D S) :
    LinearMap.adjoint h (deltav D l) k = star (h (deltav D k) l) := by
  have h1 := LinearMap.adjoint_inner_left h (deltav D k) (deltav D l)
  rw [inner_deltav_right, ← inner_conj_symm, inner_deltav_right, starRingEnd_apply,
    star_star] at h1
  rw [← h1, star_star]

/-! ## The operator tensor (CoqQ `ten_lfun`, `hstensor.v:1319`) -/

/-- Operator tensor of labelled linear maps, defined on the canonical basis by
`δ_k ↦ f δ_{k|S₁} ⊗ᵥ g δ_{k|S₂}`. CoqQ `ten_lfun` (`hstensor.v:1319`).
Scoped notation: `f ⊗ᶠ g`. -/
noncomputable def tenf (f : LinM D S₁ T₁) (g : LinM D S₂ T₂) :
    LinM D (S₁ ∪ S₂) (T₁ ∪ T₂) :=
  (EuclideanSpace.basisFun (QIdx D (S₁ ∪ S₂)) ℂ).toBasis.constr ℂ fun k =>
    tenv D (f (deltav D (QIdx.res D subset_union_left k)))
      (g (deltav D (QIdx.res D subset_union_right k)))

@[inherit_doc tenf]
scoped infixl:100 " ⊗ᶠ " => tenf _

/-! ## H-16: behavior on the basis, bilinearity -/

/-- CoqQ `tenf_dv` (`hstensor.v:1501`): value on basis kets. -/
@[simp, HS_simps]
theorem tenf_deltav (f : LinM D S₁ T₁) (g : LinM D S₂ T₂) (k : QIdx D (S₁ ∪ S₂)) :
    tenf D f g (deltav D k) =
      tenv D (f (deltav D (QIdx.res D subset_union_left k)))
        (g (deltav D (QIdx.res D subset_union_right k))) := by
  have hk : deltav D k = (EuclideanSpace.basisFun (QIdx D (S₁ ∪ S₂)) ℂ).toBasis k := by
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, deltav_def]
  rw [hk]
  exact Module.Basis.constr_basis _ ℂ _ k

theorem tenf_add_left (f₁ f₂ : LinM D S₁ T₁) (g : LinM D S₂ T₂) :
    tenf D (f₁ + f₂) g = tenf D f₁ g + tenf D f₂ g :=
  linM_ext D fun k => by
    simp only [tenf_deltav, LinearMap.add_apply, tenv_add_left]

theorem tenf_add_right (f : LinM D S₁ T₁) (g₁ g₂ : LinM D S₂ T₂) :
    tenf D f (g₁ + g₂) = tenf D f g₁ + tenf D f g₂ :=
  linM_ext D fun k => by
    simp only [tenf_deltav, LinearMap.add_apply, tenv_add_right]

theorem tenf_smul_left (c : ℂ) (f : LinM D S₁ T₁) (g : LinM D S₂ T₂) :
    tenf D (c • f) g = c • tenf D f g :=
  linM_ext D fun k => by
    simp only [tenf_deltav, LinearMap.smul_apply, tenv_smul_left]

theorem tenf_smul_right (c : ℂ) (f : LinM D S₁ T₁) (g : LinM D S₂ T₂) :
    tenf D f (c • g) = c • tenf D f g :=
  linM_ext D fun k => by
    simp only [tenf_deltav, LinearMap.smul_apply, tenv_smul_right]

@[simp]
theorem tenf_zero_left (g : LinM D S₂ T₂) :
    tenf D (0 : LinM D S₁ T₁) g = 0 :=
  linM_ext D fun k => by
    simp only [tenf_deltav, LinearMap.zero_apply, tenv_zero_left]

@[simp]
theorem tenf_zero_right (f : LinM D S₁ T₁) :
    tenf D f (0 : LinM D S₂ T₂) = 0 :=
  linM_ext D fun k => by
    simp only [tenf_deltav, LinearMap.zero_apply, tenv_zero_right]

/-! ## H-16: outer products, `tenf_apply`, interchange -/

/-- CoqQ `tenf_outp` (`hstensor.v:1509`): tensor of outer products is the outer
product of tensors — *unconditionally* (CoqQ's disjointness is not needed). -/
theorem tenf_outerLM (u : HS D T₁) (v : HS D S₁) (w : HS D T₂) (t : HS D S₂) :
    tenf D (outerLM u v) (outerLM w t) = outerLM (tenv D u w) (tenv D v t) :=
  linM_ext D fun k => PiLp.ext fun l => by
    simp only [tenf_deltav, outerLM_apply, tenv_apply, PiLp.smul_apply, smul_eq_mul,
      inner_deltav_right, star_mul']
    ring

/-- CoqQ (`hstensor.v:1545`): on a *disjoint* union of domains the operator
tensor acts factorwise on vector tensors (no condition on the codomains). -/
theorem tenf_apply (hd : Disjoint S₁ S₂) (f : LinM D S₁ T₁) (g : LinM D S₂ T₂)
    (u : HS D S₁) (v : HS D S₂) :
    tenf D f g (tenv D u v) = tenv D (f u) (g v) := by
  have h : (tenvBil D).compr₂ (tenf D f g) = (tenvBil D).compl₁₂ f g := by
    refine LinearMap.ext_basis (EuclideanSpace.basisFun (QIdx D S₁) ℂ).toBasis
      (EuclideanSpace.basisFun (QIdx D S₂) ℂ).toBasis fun k l => ?_
    have hk : (EuclideanSpace.basisFun (QIdx D S₁) ℂ).toBasis k = deltav D k := by
      simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, deltav_def]
    have hl : (EuclideanSpace.basisFun (QIdx D S₂) ℂ).toBasis l = deltav D l := by
      simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, deltav_def]
    rw [hk, hl]
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, tenvBil_apply]
    rw [deltav_merge D hd, tenf_deltav, QIdx.res_merge_left, QIdx.res_merge_right D hd]
  simpa only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, tenvBil_apply] using
    LinearMap.congr_fun (LinearMap.congr_fun h u) v

/-- **Interchange law**, CoqQ `tenf_comp` (`hstensor.v:1558`). Only the *middle*
label sets (domains of the outer factors) need to be disjoint. -/
theorem tenf_comp (hd : Disjoint T₁ T₂) (f₁ : LinM D T₁ U₁) (g₁ : LinM D T₂ U₂)
    (f₂ : LinM D S₁ T₁) (g₂ : LinM D S₂ T₂) :
    tenf D (f₁ ∘ₗ f₂) (g₁ ∘ₗ g₂) = tenf D f₁ g₁ ∘ₗ tenf D f₂ g₂ :=
  linM_ext D fun k => by
    simp only [LinearMap.comp_apply, tenf_deltav, tenf_apply D hd]

/-! ## H-16: adjoint, conjugation, transpose — all unconditional -/

/-- CoqQ `tenf_adj` (`hstensor.v:1566`) — *unconditionally*. -/
@[simp]
theorem adjoint_tenf (f : LinM D S₁ T₁) (g : LinM D S₂ T₂) :
    LinearMap.adjoint (tenf D f g) =
      tenf D (LinearMap.adjoint f) (LinearMap.adjoint g) :=
  linM_ext D fun l => PiLp.ext fun k => by
    simp only [adjoint_deltav_apply, tenf_deltav, tenv_apply, star_mul']

/-- CoqQ `tenf_conj` (`hstensor.v:1571`) — *unconditionally*. -/
@[simp]
theorem conjLM_tenf (f : LinM D S₁ T₁) (g : LinM D S₂ T₂) :
    conjLM (tenf D f g) = tenf D (conjLM f) (conjLM g) :=
  linM_ext D fun k => PiLp.ext fun l => by
    simp only [conjLM_apply, conjV_deltav, conjV_apply, tenf_deltav, tenv_apply,
      star_mul']

/-- CoqQ `tenf_tr` (`hstensor.v:1576`) — *unconditionally*. -/
@[simp]
theorem transposeLM_tenf (f : LinM D S₁ T₁) (g : LinM D S₂ T₂) :
    transposeLM (tenf D f g) = tenf D (transposeLM f) (transposeLM g) := by
  rw [← adjoint_conjLM, conjLM_tenf, adjoint_tenf, adjoint_conjLM, adjoint_conjLM]

/-- CoqQ `tenf11`: the tensor of identities is the identity — with *no cast*,
since `tenf` already lands in `EndM D (S ∪ T)`. -/
@[simp]
theorem tenf_one_one : tenf D (1 : EndM D S) (1 : EndM D T) = 1 :=
  linM_ext D fun k => by
    simp only [tenf_deltav, Module.End.one_apply]
    exact (deltav_split D k).symm

/-! ## H-17: cast laws — associativity, commutativity, unit

All unconditional, and stated for arbitrary proofs of the label-set equalities
(proof irrelevance), so `simp` matches any cast of that shape. -/

/-- CoqQ `tenf_castA` (`hstensor.v:1649`): associativity up to cast. -/
@[simp, cast_simps]
theorem tenf_castA (h₁ : S₁ ∪ (S₂ ∪ S₃) = (S₁ ∪ S₂) ∪ S₃)
    (h₂ : T₁ ∪ (T₂ ∪ T₃) = (T₁ ∪ T₂) ∪ T₃) (f : LinM D S₁ T₁) (g : LinM D S₂ T₂)
    (h : LinM D S₃ T₃) :
    castF D h₁ h₂ (tenf D f (tenf D g h)) = tenf D (tenf D f g) h :=
  linM_ext D fun k => PiLp.ext fun l => by
    simp only [castF_apply, castH_deltav, tenf_deltav, castH_apply, tenv_apply,
      QIdx.res_cast, QIdx.res_res]
    ring

/-- CoqQ `tenf_castC` (`hstensor.v:1660`): commutativity up to cast. -/
@[simp, cast_simps]
theorem tenf_castC (h₁ : S₁ ∪ S₂ = S₂ ∪ S₁) (h₂ : T₁ ∪ T₂ = T₂ ∪ T₁)
    (f : LinM D S₁ T₁) (g : LinM D S₂ T₂) :
    castF D h₁ h₂ (tenf D f g) = tenf D g f :=
  linM_ext D fun k => PiLp.ext fun l => by
    simp only [castF_apply, castH_deltav, tenf_deltav, castH_apply, tenv_apply,
      QIdx.res_cast]
    ring

/-- CoqQ `tenf_cast1r` (`hstensor.v:1670`): the empty-register identity is a
right unit up to cast. -/
@[simp, cast_simps]
theorem tenf_cast1r (h₁ : S ∪ ∅ = S) (h₂ : T ∪ ∅ = T) (f : LinM D S T) :
    castF D h₁ h₂ (tenf D f (1 : EndM D ∅)) = f :=
  linM_ext D fun k => PiLp.ext fun l => by
    simp only [castF_apply, castH_deltav, tenf_deltav, Module.End.one_apply,
      castH_apply, tenv_apply, QIdx.res_cast, QIdx.res_self, deltav_apply,
      eq_iff_true_of_subsingleton, if_true, mul_one]

/-! ## H-19: the family operator tensor (CoqQ `tenfm`, `hstensor.v:955`) -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Sf Tf : ι → Finset L}

/-- Operator tensor of a finite family of labelled linear maps, defined on the
canonical basis by `δ_k ↦ ⨂ⱼ φ j δ_{k|Sf j}`. CoqQ `tenfm` (`hstensor.v:955`). -/
noncomputable def tenfFamily (φ : ∀ j, LinM D (Sf j) (Tf j)) :
    LinM D (univ.biUnion Sf) (univ.biUnion Tf) :=
  (EuclideanSpace.basisFun (QIdx D (univ.biUnion Sf)) ℂ).toBasis.constr ℂ fun k =>
    tenvFamily D Tf fun j =>
      φ j (deltav D (QIdx.res D (subset_biUnion_of_mem Sf (mem_univ j)) k))

/-- Value of the family tensor on basis kets. -/
@[simp]
theorem tenfFamily_deltav (φ : ∀ j, LinM D (Sf j) (Tf j))
    (k : QIdx D (univ.biUnion Sf)) :
    tenfFamily D φ (deltav D k) =
      tenvFamily D Tf fun j =>
        φ j (deltav D (QIdx.res D (subset_biUnion_of_mem Sf (mem_univ j)) k)) := by
  have hk : deltav D k =
      (EuclideanSpace.basisFun (QIdx D (univ.biUnion Sf)) ℂ).toBasis k := by
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, deltav_def]
  rw [hk]
  exact Module.Basis.constr_basis _ ℂ _ k

/-- CoqQ `tenfm_apply` (`hstensor.v:1725`): on a pairwise-disjoint family of
*domains* the family tensor acts factorwise on family vector tensors. -/
theorem tenfFamily_apply (hd : Pairwise (Function.onFun Disjoint Sf))
    (φ : ∀ j, LinM D (Sf j) (Tf j)) (u : ∀ j, HS D (Sf j)) :
    tenfFamily D φ (tenvFamily D Sf u) = tenvFamily D Tf fun j => φ j (u j) := by
  conv_lhs => rw [dec_dv D (tenvFamily D Sf u)]
  rw [map_sum]
  refine PiLp.ext fun l => ?_
  simp only [HS_sum_apply, map_smul, tenfFamily_deltav, cdv_apply, PiLp.smul_apply,
    smul_eq_mul, tenvFamily_apply, ← Finset.prod_mul_distrib]
  have hφ : ∀ j, φ j (u j) (QIdx.res D (subset_biUnion_of_mem Tf (mem_univ j)) l) =
      ∑ m, u j m *
        φ j (deltav D m) (QIdx.res D (subset_biUnion_of_mem Tf (mem_univ j)) l) := by
    intro j
    conv_lhs => rw [dec_dv D (u j)]
    rw [map_sum, HS_sum_apply]
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, cdv_apply]
  simp only [hφ]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Fintype.sum_equiv (packEquiv D Sf hd) _ _ fun k => rfl

/-- CoqQ `tenfm_adj` (`hstensor.v:1743-1760`) — *unconditionally*. -/
@[simp]
theorem adjoint_tenfFamily (φ : ∀ j, LinM D (Sf j) (Tf j)) :
    LinearMap.adjoint (tenfFamily D φ) =
      tenfFamily D fun j => LinearMap.adjoint (φ j) :=
  linM_ext D fun l => PiLp.ext fun k => by
    simp only [adjoint_deltav_apply, tenfFamily_deltav, tenvFamily_apply, star_prod]

/-- CoqQ `tenfm_conj` (`hstensor.v:1743-1760`) — *unconditionally*. -/
@[simp]
theorem conjLM_tenfFamily (φ : ∀ j, LinM D (Sf j) (Tf j)) :
    conjLM (tenfFamily D φ) = tenfFamily D fun j => conjLM (φ j) :=
  linM_ext D fun k => PiLp.ext fun l => by
    simp only [conjLM_apply, conjV_deltav, conjV_apply, tenfFamily_deltav,
      tenvFamily_apply, star_prod]

/-- CoqQ `tenfm_tr` (`hstensor.v:1743-1760`) — *unconditionally*. -/
@[simp]
theorem transposeLM_tenfFamily (φ : ∀ j, LinM D (Sf j) (Tf j)) :
    transposeLM (tenfFamily D φ) = tenfFamily D fun j => transposeLM (φ j) := by
  rw [← adjoint_conjLM, conjLM_tenfFamily, adjoint_tenfFamily]
  simp only [adjoint_conjLM]

/-- Mirror of `tenvFamily_succ` for operators: the family operator tensor peels
off its head factor, up to cast — *unconditionally* (CoqQ `tenfm_recl`-style
step of `tenfm_correct`, `dirac.v:2161`). -/
theorem tenfFamily_succ {n : ℕ} {Sf Tf : Fin (n + 1) → Finset L}
    (φ : ∀ j, LinM D (Sf j) (Tf j))
    (h₁ : Sf 0 ∪ univ.biUnion (fun j : Fin n => Sf j.succ) = univ.biUnion Sf)
    (h₂ : Tf 0 ∪ univ.biUnion (fun j : Fin n => Tf j.succ) = univ.biUnion Tf) :
    castF D h₁ h₂
      (tenf D (φ 0) (tenfFamily D fun j : Fin n => φ j.succ)) = tenfFamily D φ :=
  linM_ext D fun k => PiLp.ext fun l => by
    simp only [castF_apply, castH_deltav, tenf_deltav, tenfFamily_deltav,
      castH_apply, tenv_apply, tenvFamily_apply, QIdx.res_cast, QIdx.res_res,
      Fin.prod_univ_succ]

/-- The family operator tensor over an empty index type is the identity of the
empty register, up to cast (base case of CoqQ `tenfm_correct`,
`dirac.v:2161`). -/
theorem tenfFamily_isEmpty [IsEmpty ι] (φ : ∀ j, LinM D (Sf j) (Tf j))
    (h₁ : (∅ : Finset L) = univ.biUnion Sf)
    (h₂ : (∅ : Finset L) = univ.biUnion Tf) :
    tenfFamily D φ = castF D h₁ h₂ (1 : EndM D ∅) := by
  have : Subsingleton (QIdx D (univ.biUnion Tf)) :=
    h₂ ▸ inferInstanceAs (Subsingleton (QIdx D ∅))
  refine linM_ext D fun k => PiLp.ext fun l => ?_
  simp only [tenfFamily_deltav, tenvFamily_apply, univ_eq_empty, prod_empty,
    castF_apply, castH_deltav, Module.End.one_apply, deltav_apply]
  rw [if_pos (Subsingleton.elim _ _)]

/-- Reindexing the family operator tensor along an equivalence of index types
only casts it (CoqQ handles this inside `tenfm_correct` via `\big`-reindexing,
`dirac.v:2161`). -/
theorem tenfFamily_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι)
    (φ : ∀ j, LinM D (Sf j) (Tf j))
    (h₁ : univ.biUnion Sf = univ.biUnion fun j => Sf (e j))
    (h₂ : univ.biUnion Tf = univ.biUnion fun j => Tf (e j)) :
    tenfFamily D (fun j => φ (e j)) = castF D h₁ h₂ (tenfFamily D φ) :=
  linM_ext D fun k => PiLp.ext fun l => by
    simp only [tenfFamily_deltav, tenvFamily_apply, castF_apply, castH_deltav,
      castH_apply, QIdx.res_cast]
    exact Fintype.prod_equiv e _ _ fun j => rfl

end Qhl
