import Qhl.SuperOp.Choi
import Qhl.HSpace.LiftF

/-!
# Super-operators: the tensor product `tenso`

Spec 04 §2, milestone M6 phase 3 (item Q-7), over the phase-1/2 API of
`Qhl/SuperOp/{Basic,Choi}.lean` and the operator tensor of `Qhl/HSpace/TenF.lean`.

* `tenso D E F` — Q-7, CoqQ `tenso` (`hstensor.v:2947`), defined by the same
  double `deltav`-matrix-unit sum as CoqQ's `tenso_fun`
* `tenso_outerLM_deltav` — CoqQ `tensodf` (`hstensor.v:2971`)
* `tenso_apply_tenf` — CoqQ `tenso_correct` (`hstensor.v:2983`)
* `tenso_kraussoOf` / `tenso_formsoOf` — CoqQ `tenso_krausso`/`tenso_formso`
  (`hstensor.v:3353,3383`); both come out *unconditional* here (CoqQ's
  disjointness hypothesis is an artifact of its route through `tenf_comp` —
  ours goes through `tenf_outerLM`, which needs no disjointness)
* `tenso_id_id` — the identity law, cast-free
* closure: `IsCP.tenso` (CoqQ `tenso_cp:3444`, unconditional),
  `IsQC.tenso` (CoqQ `tenso_qc:3461`), `IsQO.tenso` (CoqQ `tenso_qo:3448`),
  with exactly CoqQ's disjointness hypotheses on the latter two
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace ComplexOrder

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S T S₁ S₂ T₁ T₂ : Finset L}
variable {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]

/-! ## Sum-pushing helpers (local clones; this mathlib pin lacks
`LinearMap.sum_comp`/`comp_sum`, and `tenf` is unbundled) -/

private theorem tenf_sum_left {ι : Type*} (s : Finset ι) (f : ι → LinM D S₁ T₁)
    (g : LinM D S₂ T₂) : tenf D (∑ i ∈ s, f i) g = ∑ i ∈ s, tenf D (f i) g := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, tenf_zero_left]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, tenf_add_left, ih]

private theorem tenf_sum_right {ι : Type*} (s : Finset ι) (f : LinM D S₁ T₁)
    (g : ι → LinM D S₂ T₂) : tenf D f (∑ i ∈ s, g i) = ∑ i ∈ s, tenf D f (g i) := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, tenf_zero_right]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, tenf_add_right, ih]

private theorem tenf_sub_left (f f' : LinM D S₁ T₁) (g : LinM D S₂ T₂) :
    tenf D (f - f') g = tenf D f g - tenf D f' g := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ f', tenf_add_left, tenf_smul_left,
    neg_one_smul, ← sub_eq_add_neg]

private theorem tenf_sub_right (f : LinM D S₁ T₁) (g g' : LinM D S₂ T₂) :
    tenf D f (g - g') = tenf D f g - tenf D f g' := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ g', tenf_add_right, tenf_smul_right,
    neg_one_smul, ← sub_eq_add_neg]

/-! ## Outer-product composition helpers (Q-7 support) -/

/-- Right-composition of an outer product moves the operator into the bra slot
as its adjoint: `|u⟩⟨v| ∘ N = |u⟩⟨N† v|`. Q-7 support (mirror of
`comp_outerLM`). -/
theorem outerLM_comp_right {W : Finset L} (u : HS D T) (v : HS D S)
    (N : LinM D W S) :
    outerLM u v ∘ₗ N = outerLM u (LinearMap.adjoint N v) :=
  LinearMap.ext fun w => by
    simp only [LinearMap.comp_apply, outerLM_apply, LinearMap.adjoint_inner_left]

/-- Conjugating an outer product: `N ∘ |u⟩⟨v| ∘ N† = |N u⟩⟨N v|`. Q-7 support
(the rank-one case of a form super-operator). -/
theorem conj_outerLM (N : LinM D S T) (u v : HS D S) :
    N ∘ₗ outerLM u v ∘ₗ LinearMap.adjoint N = outerLM (N u) (N v) := by
  rw [outerLM_comp_right D u v (LinearMap.adjoint N), LinearMap.adjoint_adjoint,
    comp_outerLM]

/-! ## Q-7: the super-operator tensor (CoqQ `tenso`, `hstensor.v:2947`) -/

/-- Tensor of super-operators, by the same double matrix-unit sum as CoqQ's
`tenso_fun` (`hstensor.v:2947`): the input is decomposed over the
`|δ_i⟩⟨δ_j|` basis of `EndM D (S₁ ∪ S₂)` and each unit is sent to
`E |δ_{i|S₁}⟩⟨δ_{j|S₁}| ⊗ᶠ F |δ_{i|S₂}⟩⟨δ_{j|S₂}|`. -/
noncomputable def tenso (E : SuperOp D S₁ T₁) (F : SuperOp D S₂ T₂) :
    SuperOp D (S₁ ∪ S₂) (T₁ ∪ T₂) where
  toFun x := ∑ i, ∑ j, ⟪deltav D i, x (deltav D j)⟫ •
    tenf D (E (outerLM (deltav D (QIdx.res D subset_union_left i))
                (deltav D (QIdx.res D subset_union_left j))))
           (F (outerLM (deltav D (QIdx.res D subset_union_right i))
                (deltav D (QIdx.res D subset_union_right j))))
  map_add' x y := by
    simp only [LinearMap.add_apply, inner_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [LinearMap.smul_apply, inner_smul_right, RingHom.id_apply, mul_smul,
      Finset.smul_sum]

theorem tenso_apply (E : SuperOp D S₁ T₁) (F : SuperOp D S₂ T₂)
    (x : EndM D (S₁ ∪ S₂)) :
    tenso D E F x = ∑ i, ∑ j, ⟪deltav D i, x (deltav D j)⟫ •
      tenf D (E (outerLM (deltav D (QIdx.res D subset_union_left i))
                  (deltav D (QIdx.res D subset_union_left j))))
             (F (outerLM (deltav D (QIdx.res D subset_union_right i))
                  (deltav D (QIdx.res D subset_union_right j)))) := rfl

/-- CoqQ `tensodf` (`hstensor.v:2971`): on a matrix unit the tensor acts
factorwise on the restricted matrix units. -/
theorem tenso_outerLM_deltav (E : SuperOp D S₁ T₁) (F : SuperOp D S₂ T₂)
    (k l : QIdx D (S₁ ∪ S₂)) :
    tenso D E F (outerLM (deltav D k) (deltav D l)) =
      tenf D (E (outerLM (deltav D (QIdx.res D subset_union_left k))
                  (deltav D (QIdx.res D subset_union_left l))))
             (F (outerLM (deltav D (QIdx.res D subset_union_right k))
                  (deltav D (QIdx.res D subset_union_right l)))) := by
  rw [tenso_apply]
  simp only [outerLM_apply, inner_smul_right, dv_dot]
  rw [Fintype.sum_eq_single k fun i hi =>
    Finset.sum_eq_zero fun j _ => by simp [hi]]
  rw [Fintype.sum_eq_single l fun j hj => by simp [Ne.symm hj]]
  simp

/-- CoqQ `tenso_correct` (`hstensor.v:2983`): on a disjoint union of source
registers the super-operator tensor acts factorwise on operator tensors. -/
theorem tenso_apply_tenf (hd : Disjoint S₁ S₂) (E : SuperOp D S₁ T₁)
    (F : SuperOp D S₂ T₂) (u : EndM D S₁) (v : EndM D S₂) :
    tenso D E F (tenf D u v) = tenf D (E u) (F v) := by
  rw [eq_sum_outerLM_deltav D u, eq_sum_outerLM_deltav D v]
  simp only [tenf_sum_left, tenf_sum_right, tenf_smul_left, tenf_smul_right,
    map_sum, map_smul, tenf_outerLM, deltav_merge D hd, tenso_outerLM_deltav,
    QIdx.res_merge_left, QIdx.res_merge_right D hd]

/-! ## Q-7: Kraus and form maps tensorize (CoqQ `hstensor.v:3353,3383`) -/

/-- CoqQ `tenso_krausso` (`hstensor.v:3353`): the tensor of Kraus maps is the
Kraus map of the pairwise operator tensors — here *unconditionally* (CoqQ's
disjointness comes from its `tenf_comp` route; ours needs none). -/
theorem tenso_kraussoOf (f : κ₁ → LinM D S₁ T₁) (g : κ₂ → LinM D S₂ T₂) :
    tenso D (kraussoOf D f) (kraussoOf D g)
      = kraussoOf D fun p : κ₁ × κ₂ => tenf D (f p.1) (g p.2) := by
  refine endM_ext_outer D fun k l => ?_
  rw [tenso_outerLM_deltav]
  simp only [kraussoOf_apply, conj_outerLM, tenf_sum_left, tenf_sum_right,
    tenf_outerLM, tenf_deltav, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- CoqQ `tenso_formso` (`hstensor.v:3383`): the tensor of form maps is the
form map of the operator tensor — *unconditionally*. -/
theorem tenso_formsoOf (f : LinM D S₁ T₁) (g : LinM D S₂ T₂) :
    tenso D (formsoOf D f) (formsoOf D g) = formsoOf D (tenf D f g) := by
  rw [formsoOf_eq_kraussoOf, formsoOf_eq_kraussoOf, tenso_kraussoOf]
  refine LinearMap.ext fun x => ?_
  rw [kraussoOf_apply, Fintype.sum_prod_type, Fintype.sum_unique,
    Fintype.sum_unique, formsoOf_apply]

/-- The tensor of identity super-operators is the identity — cast-free, since
`tenso` already lands in `SuperOp D (S ∪ T) (S ∪ T)` (Q-7; the `idso`
analogue of CoqQ `tenso` unit laws). -/
theorem tenso_id_id :
    tenso D (LinearMap.id : SuperOp D S S) (LinearMap.id : SuperOp D T T)
      = LinearMap.id := by
  rw [← formsoOf_one D (S := S), ← formsoOf_one D (S := T),
    ← formsoOf_one D (S := S ∪ T), tenso_formsoOf, tenf_one_one]

/-! ## Q-7 closure: CP/QC/QO tensorize (CoqQ `hstensor.v:3444-3474`) -/

/-- The completeness sum of a pairwise-tensor Kraus family factors as the
operator tensor of the completeness sums (needs CoqQ's disjointness of the
*target* registers for the interchange law). -/
private theorem sum_adjoint_comp_tenf (hd : Disjoint T₁ T₂)
    (f : κ₁ → LinM D S₁ T₁) (g : κ₂ → LinM D S₂ T₂) :
    ∑ p : κ₁ × κ₂,
        LinearMap.adjoint (tenf D (f p.1) (g p.2)) ∘ₗ tenf D (f p.1) (g p.2)
      = tenf D (∑ a, LinearMap.adjoint (f a) ∘ₗ f a)
          (∑ b, LinearMap.adjoint (g b) ∘ₗ g b) := by
  rw [tenf_sum_left]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tenf_sum_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [adjoint_tenf, ← tenf_comp D hd]

/-- CoqQ `tenso_cp` (`hstensor.v:3444`): complete positivity tensorizes —
here *unconditionally* (CoqQ's hypothesis is an artifact of its route). -/
theorem IsCP.tenso {E : SuperOp D S₁ T₁} {F : SuperOp D S₂ T₂}
    (hE : IsCP D E) (hF : IsCP D F) : IsCP D (tenso D E F) := by
  obtain ⟨f, rfl⟩ := hE.exists_kraus
  obtain ⟨g, rfl⟩ := hF.exists_kraus
  rw [tenso_kraussoOf]
  exact isCP_kraussoOf D _

/-- CoqQ `tenso_qc` (`hstensor.v:3461`): quantum channels tensorize. Only the
disjointness of the *target* registers is needed (CoqQ also assumes the
sources disjoint). -/
theorem IsQC.tenso (hd : Disjoint T₁ T₂) {E : SuperOp D S₁ T₁}
    {F : SuperOp D S₂ T₂} (hE : IsQC D E) (hF : IsQC D F) :
    IsQC D (tenso D E F) := by
  obtain ⟨f, rfl⟩ := hE.1.exists_kraus
  obtain ⟨g, rfl⟩ := hF.1.exists_kraus
  have h1 := (isQC_kraussoOf_iff D f).mp hE
  have h2 := (isQC_kraussoOf_iff D g).mp hF
  rw [tenso_kraussoOf]
  refine (isQC_kraussoOf_iff D _).mpr ?_
  rw [sum_adjoint_comp_tenf D hd, h1, h2, tenf_one_one]

/-- `A ≤ 1` is preserved by the operator tensor of positive contractions
(the Löwner-order core of CoqQ `tenso_qo`). -/
private theorem tenf_le_one (hd : Disjoint S₁ S₂) {A : EndM D S₁}
    {B : EndM D S₂} (hA : A ≤ 1) (hB0 : B.IsPositive)
    (hB : B ≤ 1) : tenf D A B ≤ 1 := by
  rw [LinearMap.le_def]
  have key : (1 : EndM D (S₁ ∪ S₂)) - tenf D A B
      = tenf D ((1 : EndM D S₁) - A) B
        + tenf D (1 : EndM D S₁) ((1 : EndM D S₂) - B) := by
    rw [tenf_sub_left, tenf_sub_right, tenf_one_one]
    abel
  rw [key]
  exact ((tenf_isPositive D hd ((LinearMap.le_def A 1).mp hA) hB0).add
    (tenf_isPositive D hd LinearMap.isPositive_one ((LinearMap.le_def B 1).mp hB)))

/-- CoqQ `tenso_qo` (`hstensor.v:3448`): quantum operations tensorize, with
exactly CoqQ's two disjointness hypotheses. -/
theorem IsQO.tenso (hdS : Disjoint S₁ S₂) (hdT : Disjoint T₁ T₂)
    {E : SuperOp D S₁ T₁} {F : SuperOp D S₂ T₂} (hE : IsQO D E)
    (hF : IsQO D F) : IsQO D (tenso D E F) := by
  obtain ⟨f, rfl⟩ := hE.1.exists_kraus
  obtain ⟨g, rfl⟩ := hF.1.exists_kraus
  have h1 := (isQO_kraussoOf_iff D f).mp hE
  have h2 := (isQO_kraussoOf_iff D g).mp hF
  rw [tenso_kraussoOf]
  refine (isQO_kraussoOf_iff D _).mpr ?_
  rw [sum_adjoint_comp_tenf D hdT]
  exact tenf_le_one D hdS h1
    (LinearMap.isPositive_sum _ fun b _ => LinearMap.isPositive_adjoint_comp_self _)
    h2

end Qhl
