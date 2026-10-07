import Qhl.Logic.Rules
import Qhl.Program.StoreLens

/-!
# Subroutine reuse — world-embedding frame rule and store transport

Route A of the QPE-readout plan.  Two derived rules:

1. `DerivTot.embFrame_onReg` — a triple proved over a *small* world `L'`
   transports along a cell embedding `emb : L' ↪ L` into a *large* world `L`,
   framed by a fixed effect `R` on the unembedded cells.  The program
   transport is `Prog.onReg`; the assertion transport is `Assn.embFrame`.
2. `DerivTot.mapStore_pull` — a triple transports along a store lens
   (`Prog.mapStore`, `Qhl/Program/StoreLens.lean`), assertions precomposing
   with `l.get`.

Both are proved by induction on the `DerivTot` derivation — no semantic
detour, no new constructor, no axiom, nothing left open.  The cross-world
reindexing
facts feeding the atomic cases are §1b's C0 bridge (`liftF_embOp` /
`liftF_embOp_univ`: the cylindrical extension commutes with the world
embedding), its register instance C1 (`regLift_embRegister`), and the
initialisation-channel instance C2 (`Assn.embFrame_initPre`).
-/

namespace Qhl

open Finset

/-! ## §1. World embedding: cells, classical indices, spaces, operators -/

section Embed

variable {L' : Type*} [Fintype L'] [DecidableEq L']
variable {L : Type*} [Fintype L] [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]

variable (emb : L' ↪ L)

/-- The cells of an embedded subset, as a bijection of subtypes (the
`Reg.equivSig` device, for an embedding of label types). -/
noncomputable def embCellEquiv (S' : Finset L') : ↥S' ≃ ↥(S'.map emb) :=
  Equiv.ofBijective (fun i => ⟨emb i, Finset.mem_map_of_mem emb i.2⟩)
    ⟨fun a b h => Subtype.ext (emb.injective (congrArg Subtype.val h)),
     fun j => by
      obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp j.2
      exact ⟨⟨i, hi⟩, Subtype.ext hij⟩⟩

@[simp]
theorem embCellEquiv_coe (S' : Finset L') (i : ↥S') :
    (embCellEquiv emb S' i : L) = emb i := rfl

theorem emb_embCellEquiv_symm (S' : Finset L') (j : ↥(S'.map emb)) :
    emb ((embCellEquiv emb S').symm j : L') = (j : L) :=
  congrArg Subtype.val ((embCellEquiv emb S').apply_symm_apply j)

/-- Classical states of an embedded subset: reindexing along the embedding
(the `Reg.idxEquiv` device, for an embedding of label types).  The small
world's cell family is `D ∘ emb` — for a qubit world both sides are the
constant family `fun _ => 𝕢`, so this is pure relabelling. -/
noncomputable def embIdxEquiv (S' : Finset L') :
    QIdx (fun i => D (emb i)) S' ≃ QIdx D (S'.map emb) :=
  (Equiv.piCongrLeft' (fun i : ↥S' => D (emb i)) (embCellEquiv emb S')).trans
    (Equiv.piCongrRight fun j =>
      Equiv.cast (congrArg D (emb_embCellEquiv_symm emb S' j)))

/-- The labelled space of an embedded subset, by reindexing (the
`Reg.encode` device). -/
noncomputable def embHSp (S' : Finset L') :
    HS (fun i => D (emb i)) S' ≃ₗᵢ[ℂ] HS D (S'.map emb) :=
  euclCongr (embIdxEquiv D emb S')

/-- Operator transport along the embedding (the `Reg.op` device):
conjugation by the reindexing isometry. -/
noncomputable def embOp (S' : Finset L') (f : EndM (fun i => D (emb i)) S') :
    EndM D (S'.map emb) :=
  (embHSp D emb S').toLinearEquiv.conj f

variable {D}

theorem embOp_apply (S' : Finset L') (f : EndM (fun i => D (emb i)) S')
    (v : HS D (S'.map emb)) :
    embOp D emb S' f v = embHSp D emb S' (f ((embHSp D emb S').symm v)) := rfl

@[simp]
theorem embOp_zero (S' : Finset L') :
    embOp D emb S' (0 : EndM (fun i => D (emb i)) S') = 0 :=
  map_zero _

@[simp]
theorem embOp_one (S' : Finset L') :
    embOp D emb S' (1 : EndM (fun i => D (emb i)) S') = 1 := by
  refine LinearMap.ext fun v => ?_
  simp [embOp_apply]

theorem embOp_comp (S' : Finset L') (f g : EndM (fun i => D (emb i)) S') :
    embOp D emb S' (f ∘ₗ g) = embOp D emb S' f ∘ₗ embOp D emb S' g := by
  refine LinearMap.ext fun v => ?_
  simp [embOp_apply]

theorem embOp_sub (S' : Finset L') (f g : EndM (fun i => D (emb i)) S') :
    embOp D emb S' (f - g) = embOp D emb S' f - embOp D emb S' g :=
  map_sub _ _ _

theorem embOp_sum {ι : Type*} (S' : Finset L') (s : Finset ι)
    (f : ι → EndM (fun i => D (emb i)) S') :
    embOp D emb S' (∑ i ∈ s, f i) = ∑ i ∈ s, embOp D emb S' (f i) :=
  map_sum _ _ _

theorem adjoint_embOp (S' : Finset L') (f : EndM (fun i => D (emb i)) S') :
    LinearMap.adjoint (embOp D emb S' f) = embOp D emb S' (LinearMap.adjoint f) :=
  adjoint_conj_isometryEquiv _ _

theorem embOp_isPositive (S' : Finset L') {f : EndM (fun i => D (emb i)) S'}
    (hf : f.IsPositive) : (embOp D emb S' f).IsPositive :=
  isPositive_conj_isometryEquiv hf _

theorem embOp_mono (S' : Finset L') {f g : EndM (fun i => D (emb i)) S'}
    (h : f ≤ g) : embOp D emb S' f ≤ embOp D emb S' g := by
  have hpos : (embOp D emb S' (g - f)).IsPositive :=
    embOp_isPositive emb S' ((LinearMap.le_def f g).mp h)
  rw [embOp_sub] at hpos
  exact (LinearMap.le_def _ _).mpr hpos

theorem isEffect_embOp (S' : Finset L') {f : EndM (fun i => D (emb i)) S'}
    (hf : IsEffect f) : IsEffect (embOp D emb S' f) := by
  constructor
  · have h := embOp_mono emb S' hf.1
    rwa [embOp_zero] at h
  · have h := embOp_mono emb S' hf.2
    rwa [embOp_one] at h

/-! ### §1b. Coherence of `embIdxEquiv` with restriction, and the C0 bridge

The reindexing calculus behind C0/C1/C2: `embIdxEquiv` is a pure relabelling,
so it is characterised by its action on restrictions of *total* classical
states (`embIdxEquiv_restrict`, the analogue of `Reg.idxEquiv_restrict` of
`Qhl/Logic/WpChain.lean`), commutes with `QIdx.res` on both sides
(`embIdxEquiv_res` / `res_embIdxEquiv_symm`), and carries `deltav` to `deltav`
(`embHSp_deltav` / `embOp_deltav_apply`).  On top of these, `liftF_embOp` is
the subset-level C0 statement: cylindrical extension commutes with the world
embedding.  Its proof avoids any Kronecker-delta *splitting* by factoring the
whole-world extension through the intermediate set `S'.map emb ⊆ T'.map emb`
(`liftF_liftF` supplies the collapse), so only a delta *reindexing* remains. -/

/-- Transport of a value of a dependent family along an equality of labels
(`Eq.rec`-free: the `Equiv.cast` collapses by `subst`). -/
private theorem cast_apply_total {a b : L} (h : a = b) (m : ∀ i, D i) :
    Equiv.cast (congrArg D h) (m a) = m b := by subst h; rfl

/-- Two casts of the components of a small-world classical state at equal
cells agree (proof irrelevance after `subst`). -/
private theorem embCast_val_eq {T' : Finset L'} (i j : ↥T') (hij : i = j) {b : L}
    (hi : emb ↑i = b) (hj : emb ↑j = b) (v : QIdx (fun i => D (emb i)) T') :
    Equiv.cast (congrArg D hi) (v i) = Equiv.cast (congrArg D hj) (v j) := by
  subst hij; rfl

/-- `embIdxEquiv` on the restriction of a total classical state of the large
world: pure relabelling (the `Reg.idxEquiv_restrict` analogue). -/
theorem embIdxEquiv_restrict (S' : Finset L') (m : ∀ i, D i) :
    embIdxEquiv D emb S' (fun i : ↥S' => m (emb i))
      = fun x : ↥(S'.map emb) => m x := by
  funext x
  exact cast_apply_total (emb_embCellEquiv_symm emb S' x) m

theorem embIdxEquiv_symm_restrict (S' : Finset L') (m : ∀ i, D i) :
    (embIdxEquiv D emb S').symm (fun x : ↥(S'.map emb) => m x)
      = fun i : ↥S' => m (emb i) := by
  rw [Equiv.symm_apply_eq]
  exact (embIdxEquiv_restrict emb S' m).symm

/-- `embIdxEquiv` commutes with `QIdx.res` (forward form). -/
theorem embIdxEquiv_res {S' T' : Finset L'} (hsub : S' ⊆ T')
    (hm : S'.map emb ⊆ T'.map emb) (v : QIdx (fun i => D (emb i)) T') :
    embIdxEquiv D emb S' (QIdx.res (fun i => D (emb i)) hsub v)
      = QIdx.res D hm (embIdxEquiv D emb T' v) := by
  funext x
  change Equiv.cast (congrArg D (emb_embCellEquiv_symm emb S' x))
      (v ⟨((embCellEquiv emb S').symm x : L'),
        hsub ((embCellEquiv emb S').symm x).2⟩)
    = Equiv.cast (congrArg D (emb_embCellEquiv_symm emb T' ⟨(x : L), hm x.2⟩))
        (v ((embCellEquiv emb T').symm ⟨(x : L), hm x.2⟩))
  exact embCast_val_eq emb
    ⟨((embCellEquiv emb S').symm x : L'), hsub ((embCellEquiv emb S').symm x).2⟩
    ((embCellEquiv emb T').symm ⟨(x : L), hm x.2⟩)
    (Subtype.ext (emb.injective ((emb_embCellEquiv_symm emb S' x).trans
      (emb_embCellEquiv_symm emb T' ⟨(x : L), hm x.2⟩).symm)))
    (emb_embCellEquiv_symm emb S' x)
    (emb_embCellEquiv_symm emb T' ⟨(x : L), hm x.2⟩) v

/-- `embIdxEquiv` commutes with `QIdx.res` (inverse form — the shape the
`liftF` entry computations produce). -/
theorem res_embIdxEquiv_symm {S' T' : Finset L'} (hsub : S' ⊆ T')
    (hm : S'.map emb ⊆ T'.map emb) (w : QIdx D (T'.map emb)) :
    QIdx.res (fun i => D (emb i)) hsub ((embIdxEquiv D emb T').symm w)
      = (embIdxEquiv D emb S').symm (QIdx.res D hm w) := by
  apply (embIdxEquiv D emb S').injective
  rw [Equiv.apply_symm_apply,
    embIdxEquiv_res emb hsub hm ((embIdxEquiv D emb T').symm w),
    Equiv.apply_symm_apply]

/-- `embHSp` carries basis kets to basis kets. -/
theorem embHSp_deltav (S' : Finset L') (t : QIdx (fun i => D (emb i)) S') :
    embHSp D emb S' (deltav (fun i => D (emb i)) t)
      = deltav D (embIdxEquiv D emb S' t) :=
  euclCongr_single (embIdxEquiv D emb S') t 1

/-- Matrix entries of `embOp`: a pure relabelling of the entries of `f`. -/
theorem embOp_deltav_apply (S' : Finset L') (f : EndM (fun i => D (emb i)) S')
    (x y : QIdx D (S'.map emb)) :
    embOp D emb S' f (deltav D x) y
      = f (deltav (fun i => D (emb i)) ((embIdxEquiv D emb S').symm x))
          ((embIdxEquiv D emb S').symm y) := by
  have hx : (embHSp D emb S').symm (deltav D x)
      = deltav (fun i => D (emb i)) ((embIdxEquiv D emb S').symm x) := by
    apply (embHSp D emb S').injective
    rw [LinearIsometryEquiv.apply_symm_apply, embHSp_deltav, Equiv.apply_symm_apply]
  rw [embOp_apply, hx]
  rfl

/-- The Kronecker-delta condition transports along a propositional equality of
the restricted label set (proof irrelevance after `subst`). -/
private theorem res_eq_res_iff_of_eq {A B U : Finset L} (hAB : A = B) (h₁ : A ⊆ U)
    (h₂ : B ⊆ U) (k l : QIdx D U) :
    QIdx.res D h₁ l = QIdx.res D h₁ k ↔ QIdx.res D h₂ l = QIdx.res D h₂ k := by
  subst hAB
  exact Iff.rfl

/-- **C0, subset form**: the cylindrical extension between the *images* of two
nested small-world label sets commutes with the world embedding. -/
theorem liftF_embOp {S' T' : Finset L'} (hsub : S' ⊆ T')
    (hm : S'.map emb ⊆ T'.map emb) (f : EndM (fun i => D (emb i)) S') :
    liftF D hm (embOp D emb S' f)
      = embOp D emb T' (liftF (fun i => D (emb i)) hsub f) := by
  have hm2 : (T' \ S').map emb ⊆ T'.map emb :=
    Finset.map_subset_map.mpr sdiff_subset
  refine linM_ext D fun k => PiLp.ext fun l => ?_
  rw [liftF_deltav_apply, embOp_deltav_apply, embOp_deltav_apply, liftF_deltav_apply,
    res_embIdxEquiv_symm emb hsub hm k, res_embIdxEquiv_symm emb hsub hm l]
  refine congrArg₂ (· * ·) rfl (if_congr ?_ rfl rfl)
  rw [res_embIdxEquiv_symm emb sdiff_subset hm2 l,
    res_embIdxEquiv_symm emb sdiff_subset hm2 k, Equiv.apply_eq_iff_eq]
  exact res_eq_res_iff_of_eq (Finset.map_sdiff T' S').symm sdiff_subset hm2 k l

/-- `embOp` carries an outer product of basis kets to the outer product of the
reindexed basis kets (the Kraus operators of the initialisation channel are of
this shape). -/
theorem embOp_outerLM_deltav (S' : Finset L') (x y : QIdx (fun i => D (emb i)) S') :
    embOp D emb S' (outerLM (deltav (fun i => D (emb i)) x)
        (deltav (fun i => D (emb i)) y))
      = outerLM (deltav D (embIdxEquiv D emb S' x))
          (deltav D (embIdxEquiv D emb S' y)) := by
  refine LinearMap.ext fun v => ?_
  rw [embOp_apply, outerLM_apply, map_smul, outerLM_apply, embHSp_deltav]
  congr 1
  rw [← embHSp_deltav, ← (embHSp D emb S').inner_map_map,
    LinearIsometryEquiv.apply_symm_apply]

/-- The reindexing fixes the all-defaults classical state (`∣0…0⟩ ↦ ∣0…0⟩`). -/
theorem embIdxEquiv_default [∀ i, Inhabited (D i)] (S' : Finset L') :
    embIdxEquiv D emb S' (default : QIdx (fun i => D (emb i)) S')
      = (default : QIdx D (S'.map emb)) :=
  embIdxEquiv_restrict emb S' fun _ => default

end Embed

/-! ## §2. Effect algebra for the tensor with a frame -/

section TenEffect

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]

theorem tenf_sub_left {S T : Finset L} (f₁ f₂ : EndM D S) (g : EndM D T) :
    tenf D (f₁ - f₂) g = tenf D f₁ g - tenf D f₂ g := by
  rw [sub_eq_add_neg, sub_eq_add_neg, tenf_add_left,
    show -f₂ = (-1 : ℂ) • f₂ by simp, tenf_smul_left]
  simp

theorem tenf_sub_right {S T : Finset L} (f : EndM D S) (g₁ g₂ : EndM D T) :
    tenf D f (g₁ - g₂) = tenf D f g₁ - tenf D f g₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, tenf_add_right,
    show -g₂ = (-1 : ℂ) • g₂ by simp, tenf_smul_right]
  simp

theorem tenf_sum_left {ι : Type*} {S T : Finset L} (s : Finset ι)
    (f : ι → EndM D S) (g : EndM D T) :
    tenf D (∑ i ∈ s, f i) g = ∑ i ∈ s, tenf D (f i) g := by
  induction s using Finset.cons_induction with
  | empty => simp [tenf_zero_left]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, tenf_add_left, ih]

/-- The tensor of a frame effect is monotone in the framed slot. -/
theorem tenf_le_tenf_left {S T : Finset L} (hd : Disjoint S T)
    {f₁ f₂ : EndM D S} (h : f₁ ≤ f₂) {g : EndM D T} (hg : g.IsPositive) :
    tenf D f₁ g ≤ tenf D f₂ g := by
  have hpos : (tenf D (f₂ - f₁) g).IsPositive :=
    tenf_isPositive D hd ((LinearMap.le_def f₁ f₂).mp h) hg
  rw [tenf_sub_left] at hpos
  exact (LinearMap.le_def _ _).mpr hpos

theorem tenf_le_tenf_right {S T : Finset L} (hd : Disjoint S T)
    {f : EndM D S} (hf : f.IsPositive) {g₁ g₂ : EndM D T} (h : g₁ ≤ g₂) :
    tenf D f g₁ ≤ tenf D f g₂ := by
  have hpos : (tenf D f (g₂ - g₁)).IsPositive :=
    tenf_isPositive D hd hf ((LinearMap.le_def g₁ g₂).mp h)
  rw [tenf_sub_right] at hpos
  exact (LinearMap.le_def _ _).mpr hpos

/-- The tensor of two effects on disjoint cell sets is an effect. -/
theorem isEffect_tenf {S T : Finset L} (hd : Disjoint S T)
    {f : EndM D S} {g : EndM D T} (hf : IsEffect f) (hg : IsEffect g) :
    IsEffect (tenf D f g) := by
  constructor
  · rw [show (0 : EndM D (S ∪ T)) = tenf D (0 : EndM D S) g from
      (tenf_zero_left D g).symm]
    exact tenf_le_tenf_left hd hf.1 (hg.isPositive)
  · calc tenf D f g ≤ tenf D (1 : EndM D S) g :=
          tenf_le_tenf_left hd hf.2 hg.isPositive
      _ ≤ tenf D (1 : EndM D S) 1 :=
          tenf_le_tenf_right hd (isEffect_one.isPositive) hg.2
      _ = 1 := tenf_one_one D

/-- `castF` preserves the effect predicate. -/
theorem isEffect_castF {S T : Finset L} (h : S = T) {f : EndM D S}
    (hf : IsEffect f) : IsEffect (castF D h h f) := by
  subst h
  rw [castF_rfl]
  exact hf

end TenEffect

/-! ## §3. The framed assertion `A ⊗ R` over the large world -/

section EmbFrame

variable {L' : Type*} [Fintype L'] [DecidableEq L']
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}
variable (emb : L' ↪ L)

/-- The embedded image of the whole small world. -/
abbrev embRange : Finset L := (univ : Finset L').map emb

theorem embRange_union_sdiff :
    embRange emb ∪ ((univ : Finset L) \ embRange emb) = univ :=
  union_sdiff_of_subset (subset_univ _)

theorem disjoint_embRange_sdiff :
    Disjoint (embRange emb) ((univ : Finset L) \ embRange emb) :=
  disjoint_sdiff

variable {emb}

/-- **The framed assertion**: a small-world assertion, reindexed onto the
embedded cells and tensored with a fixed frame effect `R` on the unembedded
cells.  This is the `A ⊗ R` of the frame rule, expressed with the library's
`tenf`/`castF` vocabulary (the same normal form `liftF` uses). -/
noncomputable def Assn.embFrame (A : Assn σT (fun i => D (emb i)))
    (R : EndM D ((univ : Finset L) \ embRange emb)) (hR : IsEffect R) :
    Assn σT D where
  op σ := castF D (embRange_union_sdiff emb) (embRange_union_sdiff emb)
    (tenf D (embOp D emb univ (A.op σ)) R)
  isEffect σ := isEffect_castF _
    (isEffect_tenf (disjoint_embRange_sdiff emb)
      (isEffect_embOp emb univ (A.isEffect σ)) hR)

@[simp]
theorem Assn.embFrame_op (A : Assn σT (fun i => D (emb i)))
    (R : EndM D ((univ : Finset L) \ embRange emb)) (hR : IsEffect R) (σ : σT) :
    (A.embFrame R hR).op σ
      = castF D (embRange_union_sdiff emb) (embRange_union_sdiff emb)
          (tenf D (embOp D emb univ (A.op σ)) R) := rfl

variable {R : EndM D ((univ : Finset L) \ embRange emb)} {hR : IsEffect R}

/-- Classical substitution commutes with framing (definitionally). -/
theorem Assn.embFrame_comp (A : Assn σT (fun i => D (emb i))) (f : σT → σT) :
    (A.comp f).embFrame R hR = (A.embFrame R hR).comp f := rfl

/-- The classical mask commutes with framing (the frame acts only on the
quantum component; the closed branch is `0 ⊗ R = 0`). -/
theorem Assn.embFrame_mask (A : Assn σT (fun i => D (emb i))) (φ : σT → Prop) :
    (A.mask φ).embFrame R hR = (A.embFrame R hR).mask φ := by
  refine Assn.ext (funext fun σ => ?_)
  by_cases h : φ σ
  · rw [Assn.embFrame_op, Assn.mask_op_of_pos h, Assn.mask_op_of_pos h,
      Assn.embFrame_op]
  · rw [Assn.embFrame_op, Assn.mask_op_of_neg h, Assn.mask_op_of_neg h,
      embOp_zero, tenf_zero_left, map_zero]

theorem Assn.embFrame_mand (A : Assn σT (fun i => D (emb i))) (b : σT → Bool) :
    (A.mand b).embFrame R hR = (A.embFrame R hR).mand b :=
  Assn.embFrame_mask A _

theorem Assn.embFrame_mandNot (A : Assn σT (fun i => D (emb i))) (b : σT → Bool) :
    (A.mandNot b).embFrame R hR = (A.embFrame R hR).mandNot b :=
  Assn.embFrame_mask A _

/-- The branching combinator commutes with framing. -/
theorem Assn.embFrame_guard (b : σT → Bool) (A₁ A₀ : Assn σT (fun i => D (emb i))) :
    (Assn.guard b A₁ A₀).embFrame R hR
      = Assn.guard b (A₁.embFrame R hR) (A₀.embFrame R hR) := by
  refine Assn.ext (funext fun σ => ?_)
  by_cases h : b σ = true
  · rw [Assn.embFrame_op, Assn.guard_op_of_true h, Assn.guard_op_of_true h,
      Assn.embFrame_op]
  · rw [Bool.not_eq_true] at h
    rw [Assn.embFrame_op, Assn.guard_op_of_false h, Assn.guard_op_of_false h,
      Assn.embFrame_op]

/-- Framing is monotone: the quantum half of (R-Conseq) survives the frame,
because the frame effect is positive. -/
theorem Assn.embFrame_mono {A B : Assn σT (fun i => D (emb i))} (h : A ≤ B) :
    A.embFrame R hR ≤ B.embFrame R hR := by
  intro σ
  rw [Assn.embFrame_op, Assn.embFrame_op, castF_le_castF_iff]
  exact tenf_le_tenf_left (disjoint_embRange_sdiff emb)
    (embOp_mono emb univ (h σ)) hR.isPositive

/-- Identity on both the embedded subsystem and its complement gives the
identity assertion on the whole register. -/
theorem Assn.embFrame_one_one :
    (Assn.one : Assn σT (fun i => D (emb i))).embFrame
      (1 : EndM D (univ \ embRange emb)) isEffect_one = Assn.one := by
  ext σ
  simp [Assn.embFrame_op, Assn.one_op, embOp_one, tenf_one_one, castF_one]

end EmbFrame

/-! ## §4. The program transport `Prog.onReg` -/

section OnReg

variable {L' : Type*} [Fintype L'] [DecidableEq L']
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {σT : Type*}

/-- Transport a program of the small world `L'` (cell family `D ∘ emb`) into
the large world `L`, rebuilding every node and post-composing register
expressions with the embedding.  The gate and measurement payloads transfer
*unchanged*: `TSpace (fun i => D (emb i)) (r σ)` and
`TSpace D (fun j => emb (r σ j))` are definitionally equal. -/
def Prog.onReg (emb : L' ↪ L) : Prog σT (fun i => D (emb i)) → Prog σT D
  | .skip => .skip
  | .assign f => .assign f
  | .init S => .init fun σ => (S σ).map emb
  | .unitary k r U => .unitary k (fun σ j => emb (r σ j)) U
  | .measure m k r M upd => .measure m k (fun σ j => emb (r σ j)) M upd
  | .seq P₁ P₂ => .seq (P₁.onReg emb) (P₂.onReg emb)
  | .ite b P₁ P₀ => .ite b (P₁.onReg emb) (P₀.onReg emb)
  | .while b P => .while b (P.onReg emb)

end OnReg

/-! ## §5. The transformer commutations and the frame rule -/

section FrameRule

variable {L' : Type*} [Fintype L'] [DecidableEq L']
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}
variable (emb : L' ↪ L)

theorem injective_emb_comp {k : ℕ} {r : Fin k → L'} (h : Function.Injective r) :
    Function.Injective fun j => emb (r j) :=
  fun _ _ hab => h (emb.injective hab)

theorem injective_of_emb_comp {k : ℕ} {r : Fin k → L'}
    (h : Function.Injective fun j => emb (r j)) : Function.Injective r :=
  fun _ _ hab => h (congrArg emb hab)

/-- A cast of the lifted operator is absorbed into the extension (proof
irrelevance after `subst`). -/
private theorem liftF_castF_arg {S T U : Finset L} (e : S = T) (hT : T ⊆ U)
    (hS : S ⊆ U) (f : EndM D S) :
    liftF D hT (castF D e e f) = liftF D hS f := by
  subst e
  rw [castF_rfl, LinearEquiv.refl_apply]

/-- **C0 at the whole small world**: the large-world cylindrical extension of
an `embOp`-transported subset operator is the `embFrame` normal form
`castF (tenf (embOp …) 1)`.  Factoring through the intermediate label set
`S'.map emb ⊆ embRange emb ⊆ univ`, the library's `liftF_liftF` collapse plus
the subset-level bridge `liftF_embOp` do all the work: the last step is the
definition of `liftF` at `embRange emb ⊆ univ`. -/
theorem liftF_embOp_univ (S' : Finset L') (f : EndM (fun i => D (emb i)) S') :
    liftF D (subset_univ (S'.map emb)) (embOp D emb S' f)
      = castF D (embRange_union_sdiff emb) (embRange_union_sdiff emb)
          (tenf D (embOp D emb univ (liftF (fun i => D (emb i)) (subset_univ S') f))
            (1 : EndM D ((univ : Finset L) \ embRange emb))) :=
  calc liftF D (subset_univ (S'.map emb)) (embOp D emb S' f)
      = liftF D (subset_univ (embRange emb))
          (liftF D (Finset.map_subset_map.mpr (subset_univ S'))
            (embOp D emb S' f)) :=
        (liftF_liftF D (Finset.map_subset_map.mpr (subset_univ S'))
          (subset_univ (embRange emb)) (embOp D emb S' f)).symm
    _ = liftF D (subset_univ (embRange emb))
          (embOp D emb univ (liftF (fun i => D (emb i)) (subset_univ S') f)) := by
        rw [liftF_embOp emb (subset_univ S')
          (Finset.map_subset_map.mpr (subset_univ S')) f]
    _ = castF D (embRange_union_sdiff emb) (embRange_union_sdiff emb)
          (tenf D (embOp D emb univ (liftF (fun i => D (emb i)) (subset_univ S') f))
            (1 : EndM D ((univ : Finset L) \ embRange emb))) := rfl

/-! ### The register instance of C0: `Reg.op` transports along the embedding.

Local clones of `Reg.idxEquiv_apply_of_symm` / `Reg.idxEquiv_restrict`
(`Qhl/Logic/Frame.lean` / `Qhl/Logic/WpChain.lean`, not in this file's import
cone) — promotion candidates. -/

private theorem regIdxEquiv_apply_of_symm {L₀ : Type*} [DecidableEq L₀]
    {D₀ : L₀ → Type*} [∀ i, Fintype (D₀ i)] [∀ i, DecidableEq (D₀ i)] {k : ℕ}
    (r : Reg L₀ k) (t : TIdx D₀ r.toFun) (j : ↥r.sig) (i : Fin k)
    (hij : r.equivSig.symm j = i) (h2 : r i = (j : L₀)) :
    r.idxEquiv D₀ t j = Equiv.cast (congrArg D₀ h2) (t i) := by
  subst hij; rfl

private theorem regIdxEquiv_apply_equivSig {L₀ : Type*} [DecidableEq L₀]
    {D₀ : L₀ → Type*} [∀ i, Fintype (D₀ i)] [∀ i, DecidableEq (D₀ i)] {k : ℕ}
    (r : Reg L₀ k) (t : TIdx D₀ r.toFun) (j : Fin k) :
    r.idxEquiv D₀ t (r.equivSig j) = t j :=
  regIdxEquiv_apply_of_symm r t (r.equivSig j) j (Equiv.symm_apply_apply _ _) rfl

private theorem regIdxEquiv_restrict {L₀ : Type*} [DecidableEq L₀]
    {D₀ : L₀ → Type*} [∀ i, Fintype (D₀ i)] [∀ i, DecidableEq (D₀ i)] {k : ℕ}
    (r : Reg L₀ k) (m : ∀ i, D₀ i) :
    r.idxEquiv D₀ (fun j => m (r j)) = fun x : ↥r.sig => m x := by
  funext x
  obtain ⟨j, rfl⟩ := r.equivSig.surjective x
  rw [regIdxEquiv_apply_equivSig]
  rfl

/-- The signature of the embedded register is the mapped signature. -/
theorem sig_embReg {k : ℕ} (r : Fin k → L') (hr : Function.Injective r)
    (hr' : Function.Injective fun j => emb (r j)) :
    (Reg.mk (fun j => emb (r j)) hr').sig = (Reg.mk r hr).sig.map emb := by
  ext a
  simp only [Reg.sig, Finset.mem_image, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨r j, ⟨j, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, rfl⟩

/-- The inverse reindexing of the embedded image of a register signature,
evaluated at the restriction of a total classical state, is the register's own
reindexing of the pulled-back tuple. -/
private theorem embIdxEquiv_symm_total_reg {k : ℕ} (r : Reg L' k) (m : ∀ i, D i) :
    (embIdxEquiv D emb r.sig).symm (fun c : ↥(r.sig.map emb) => m ↑c)
      = r.idxEquiv (fun i => D (emb i)) (fun j => m (emb (r j))) := by
  rw [Equiv.symm_apply_eq,
    show r.idxEquiv (fun i => D (emb i)) (fun j => m (emb (r j)))
        = fun x : ↥r.sig => m (emb ↑x) from
      regIdxEquiv_restrict r (fun i : L' => m (emb i)),
    embIdxEquiv_restrict emb r.sig m]

/-- `QIdx.cast` on the restriction of a total classical state is the
restriction to the other set (pure re-wrapping). -/
private theorem qidx_cast_total {S T : Finset L} (h : S = T) (m : ∀ i, D i) :
    QIdx.cast D h (fun c : ↥S => m ↑c) = fun c : ↥T => m ↑c := rfl

/-- **The register instance of the reindexing bridge**: transporting a gate
along the embedded register is `embOp` of the small-world transport, up to the
signature cast. -/
private theorem embReg_op {k : ℕ} (r : Fin k → L') (hr : Function.Injective r)
    (hr' : Function.Injective fun j => emb (r j))
    (K : TSpace (fun i => D (emb i)) r →ₗ[ℂ] TSpace (fun i => D (emb i)) r) :
    (Reg.mk (fun j => emb (r j)) hr').op D K
      = castF D (sig_embReg emb r hr hr').symm (sig_embReg emb r hr hr').symm
          (embOp D emb (Reg.mk r hr).sig
            ((Reg.mk r hr).op (fun i => D (emb i)) K)) := by
  refine linM_ext D fun x => PiLp.ext fun y => ?_
  obtain ⟨mx, rfl⟩ : ∃ m : ∀ i, D i,
      (fun c : ↥(Reg.mk (fun j => emb (r j)) hr').sig => m ↑c) = x :=
    ⟨fun i => if h : i ∈ (Reg.mk (fun j => emb (r j)) hr').sig then x ⟨i, h⟩
      else default, funext fun c => dif_pos c.2⟩
  obtain ⟨my, rfl⟩ : ∃ m : ∀ i, D i,
      (fun c : ↥(Reg.mk (fun j => emb (r j)) hr').sig => m ↑c) = y :=
    ⟨fun i => if h : i ∈ (Reg.mk (fun j => emb (r j)) hr').sig then y ⟨i, h⟩
      else default, funext fun c => dif_pos c.2⟩
  conv_lhs => rw [← regIdxEquiv_restrict (Reg.mk (fun j => emb (r j)) hr') mx,
    ← regIdxEquiv_restrict (Reg.mk (fun j => emb (r j)) hr') my,
    Reg.op_deltav_apply]
  conv_rhs => rw [castF_apply, castH_deltav, castH_apply, qidx_cast_total,
    qidx_cast_total, embOp_deltav_apply,
    embIdxEquiv_symm_total_reg emb (Reg.mk r hr) mx,
    embIdxEquiv_symm_total_reg emb (Reg.mk r hr) my, Reg.op_deltav_apply]

/-- **C1, the central bridge** (the spike's first open obligation): the whole-world
cylindrical extension of a register operator, taken in the LARGE world at the
embedded register, equals the SMALL world's cylindrical extension transported
by `embOp` and tensored with the identity on the unembedded cells.  Register
instance of C0 (`liftF_embOp` / `liftF_embOp_univ`) through the signature
bridge `embReg_op`. -/
theorem regLift_embRegister {k : ℕ} (r : Fin k → L') (hr : Function.Injective r)
    (hr' : Function.Injective fun j => emb (r j))
    (K : TSpace (fun i => D (emb i)) r →ₗ[ℂ] TSpace (fun i => D (emb i)) r) :
    regLift (D := D) ⟨fun j => emb (r j), hr'⟩ K
      = castF D (embRange_union_sdiff emb) (embRange_union_sdiff emb)
          (tenf D (embOp D emb univ (regLift (D := fun i => D (emb i)) ⟨r, hr⟩ K))
            (1 : EndM D ((univ : Finset L) \ embRange emb))) := by
  have h1 : regLift (D := D) ⟨fun j => emb (r j), hr'⟩ K
      = liftF D (subset_univ ((Reg.mk r hr).sig.map emb))
          (embOp D emb (Reg.mk r hr).sig
            ((Reg.mk r hr).op (fun i => D (emb i)) K)) := by
    change liftF D (subset_univ (Reg.mk (fun j => emb (r j)) hr').sig)
        ((Reg.mk (fun j => emb (r j)) hr').op D K) = _
    rw [embReg_op emb r hr hr' K]
    exact liftF_castF_arg (sig_embReg emb r hr hr').symm _ _ _
  rw [h1, liftF_embOp_univ emb (Reg.mk r hr).sig
    ((Reg.mk r hr).op (fun i => D (emb i)) K)]
  rfl

/-- The conjugation collapse: conjugating a framed effect by the embedded
register operator is framing the small-world conjugation.  This is the shape
both (Ax-Uni) and each Born-sum branch of (Ax-Meas) need; it is pure
`castF`/`tenf` interchange algebra on top of the C1 bridge. -/
theorem conj_regLift_embFrame {k : ℕ} (r : Fin k → L') (hr : Function.Injective r)
    (hr' : Function.Injective fun j => emb (r j))
    (K : TSpace (fun i => D (emb i)) r →ₗ[ℂ] TSpace (fun i => D (emb i)) r)
    (a : EndM (fun i => D (emb i)) (univ : Finset L'))
    (R : EndM D ((univ : Finset L) \ embRange emb)) :
    LinearMap.adjoint (regLift (D := D) ⟨fun j => emb (r j), hr'⟩ K)
        ∘ₗ castF D (embRange_union_sdiff emb) (embRange_union_sdiff emb)
            (tenf D (embOp D emb univ a) R)
        ∘ₗ regLift (D := D) ⟨fun j => emb (r j), hr'⟩ K
      = castF D (embRange_union_sdiff emb) (embRange_union_sdiff emb)
          (tenf D (embOp D emb univ
              (LinearMap.adjoint (regLift (D := fun i => D (emb i)) ⟨r, hr⟩ K)
                ∘ₗ a ∘ₗ regLift (D := fun i => D (emb i)) ⟨r, hr⟩ K)) R) := by
  rw [regLift_embRegister emb r hr hr' K, castF_adj, adjoint_tenf, adjoint_embOp,
    LinearMap.adjoint_one, ← castF_comp, ← castF_comp,
    ← tenf_comp D (disjoint_embRange_sdiff emb),
    ← tenf_comp D (disjoint_embRange_sdiff emb)]
  simp only [Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
  rw [← embOp_comp, ← embOp_comp]

/-- The conjugation collapse at the subset level (the C0 analogue of
`conj_regLift_embFrame`): conjugating a framed effect by the lifted `embOp` of
a subset operator is framing the small-world conjugation.  Each Kraus branch
of (Ax-Init) is of this shape. -/
theorem conj_liftF_embFrame (S' : Finset L') (K : EndM (fun i => D (emb i)) S')
    (a : EndM (fun i => D (emb i)) (univ : Finset L'))
    (R : EndM D ((univ : Finset L) \ embRange emb)) :
    LinearMap.adjoint (liftF D (subset_univ (S'.map emb)) (embOp D emb S' K))
        ∘ₗ castF D (embRange_union_sdiff emb) (embRange_union_sdiff emb)
            (tenf D (embOp D emb univ a) R)
        ∘ₗ liftF D (subset_univ (S'.map emb)) (embOp D emb S' K)
      = castF D (embRange_union_sdiff emb) (embRange_union_sdiff emb)
          (tenf D (embOp D emb univ
              (LinearMap.adjoint (liftF (fun i => D (emb i)) (subset_univ S') K)
                ∘ₗ a ∘ₗ liftF (fun i => D (emb i)) (subset_univ S') K)) R) := by
  rw [liftF_embOp_univ emb S' K, castF_adj, adjoint_tenf, adjoint_embOp,
    LinearMap.adjoint_one, ← castF_comp, ← castF_comp,
    ← tenf_comp D (disjoint_embRange_sdiff emb),
    ← tenf_comp D (disjoint_embRange_sdiff emb)]
  simp only [Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
  rw [← embOp_comp, ← embOp_comp]

/-- The dual of the initialisation channel, in Kraus form: the Born-type sum
of conjugations by the lifted `|0⟩⟨x|` family (`liftSO_kraussoOf` +
`dualSO_kraussoOf`), world-generic. -/
private theorem dualSO_initLift_apply {L₀ : Type*} [Fintype L₀] [DecidableEq L₀]
    {D₀ : L₀ → Type*} [∀ i, Fintype (D₀ i)] [∀ i, DecidableEq (D₀ i)]
    [∀ i, Inhabited (D₀ i)] (S : Finset L₀) (a : EndM D₀ (univ : Finset L₀)) :
    dualSO D₀ (initLift S) a
      = ∑ x : QIdx D₀ S,
          LinearMap.adjoint (liftF D₀ (subset_univ S)
              (outerLM (deltav D₀ (default : QIdx D₀ S)) (deltav D₀ x)))
            ∘ₗ a ∘ₗ liftF D₀ (subset_univ S)
              (outerLM (deltav D₀ (default : QIdx D₀ S)) (deltav D₀ x)) := by
  rw [show initLift (D := D₀) S = liftSO D₀ (subset_univ S) (initSO D₀ S) from rfl,
    show initSO D₀ S = kraussoOf D₀ (fun x : QIdx D₀ S =>
        outerLM (deltav D₀ (default : QIdx D₀ S)) (deltav D₀ x)) from rfl,
    liftSO_kraussoOf, dualSO_kraussoOf, kraussoOf_apply]
  exact Finset.sum_congr rfl fun x _ => by rw [LinearMap.adjoint_adjoint]

variable {R : EndM D ((univ : Finset L) \ embRange emb)} {hR : IsEffect R}

/-- (Ax-Uni) commutes with framing: the framed precondition of the embedded
gate is the frame of the small-world precondition. -/
theorem Assn.embFrame_unitaryPre (A : Assn σT (fun i => D (emb i))) {k : ℕ}
    (r : RegExpr σT L' k)
    (U : ∀ σ, UnitaryOp (TSpace (fun i => D (emb i)) (r σ))) :
    (A.unitaryPre r U).embFrame R hR
      = (A.embFrame R hR).unitaryPre (fun σ j => emb (r σ j)) U := by
  refine Assn.ext (funext fun σ => ?_)
  by_cases h : Function.Injective (r σ)
  · have h' : Function.Injective fun j => emb (r σ j) := injective_emb_comp emb h
    rw [Assn.embFrame_op, Assn.unitaryPre_op_of_dist A r U h,
      Assn.unitaryPre_op_of_dist _ _ _ h', Assn.embFrame_op]
    have hh := conj_regLift_embFrame emb (r σ) h h' (U σ) (A.op σ) R
    exact hh.symm
  · have h' : ¬ Function.Injective fun j => emb (r σ j) :=
      fun hc => h (injective_of_emb_comp emb hc)
    rw [Assn.embFrame_op, Assn.unitaryPre_op_of_not_dist A r U h,
      Assn.unitaryPre_op_of_not_dist _ _ _ h', embOp_zero, tenf_zero_left, map_zero]

/-- (Ax-Meas) commutes with framing: the Born sum passes through `embOp`,
`tenf` and `castF` linearly, and each branch is the conjugation collapse. -/
theorem Assn.embFrame_measurePre (A : Assn σT (fun i => D (emb i))) {m k : ℕ}
    (r : RegExpr σT L' k)
    (M : ∀ σ, QMeasure m (TSpace (fun i => D (emb i)) (r σ)))
    (upd : Fin m → σT → σT) :
    (A.measurePre r M upd).embFrame R hR
      = (A.embFrame R hR).measurePre (fun σ j => emb (r σ j)) M upd := by
  refine Assn.ext (funext fun σ => ?_)
  by_cases h : Function.Injective (r σ)
  · have h' : Function.Injective fun j => emb (r σ j) := injective_emb_comp emb h
    rw [Assn.embFrame_op, Assn.measurePre_op_of_dist A r M upd h,
      Assn.measurePre_op_of_dist _ _ _ _ h', embOp_sum, tenf_sum_left, map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      (conj_regLift_embFrame emb (r σ) h h' ((M σ).M i) (A.op (upd i σ)) R).symm
  · have h' : ¬ Function.Injective fun j => emb (r σ j) :=
      fun hc => h (injective_of_emb_comp emb hc)
    rw [Assn.embFrame_op, Assn.measurePre_op_of_not_dist A r M upd h,
      Assn.measurePre_op_of_not_dist _ _ _ _ h', embOp_zero, tenf_zero_left, map_zero]

/-- **C2, the init bridge** (the spike's second open obligation): (Ax-Init) commutes with
framing.  Both sides become Born-type Kraus sums of conjugations by
`liftF (outerLM ∣0…0⟩ ⟨x∣)` (`dualSO_initLift_apply`); the large-world sum is
reindexed along `embIdxEquiv` (`Fintype.sum_equiv`), each summand is the
subset-level conjugation collapse `conj_liftF_embFrame` through the Kraus
coherences `embOp_outerLM_deltav` and `embIdxEquiv_default`. -/
theorem Assn.embFrame_initPre (A : Assn σT (fun i => D (emb i)))
    (S : σT → Finset L') :
    (A.initPre S).embFrame R hR
      = (A.embFrame R hR).initPre fun σ => (S σ).map emb := by
  refine Assn.ext (funext fun σ => ?_)
  rw [Assn.embFrame_op, Assn.initPre_op, Assn.initPre_op, Assn.embFrame_op,
    dualSO_initLift_apply, dualSO_initLift_apply, embOp_sum, tenf_sum_left, map_sum]
  refine Fintype.sum_equiv (embIdxEquiv D emb (S σ)) _ _ fun x => ?_
  rw [show outerLM (deltav D (default : QIdx D ((S σ).map emb)))
        (deltav D (embIdxEquiv D emb (S σ) x))
      = embOp D emb (S σ)
          (outerLM (deltav (fun i => D (emb i))
              (default : QIdx (fun i => D (emb i)) (S σ)))
            (deltav (fun i => D (emb i)) x)) from by
    rw [embOp_outerLM_deltav, embIdxEquiv_default]]
  exact (conj_liftF_embFrame emb (S σ)
    (outerLM (deltav (fun i => D (emb i)) (default : QIdx (fun i => D (emb i)) (S σ)))
      (deltav (fun i => D (emb i)) x)) (A.op σ) R).symm

/-- **The derived frame rule for whole subprograms** — proved by induction on
the `DerivTot` derivation, from the `DerivTot` constructors alone.  A triple
over the small world `L'` transports along `emb : L' ↪ L` to the framed
triple over the large world, with an arbitrary fixed effect `R` on the
unembedded cells. -/
theorem DerivTot.embFrame_onReg
    {A B : Assn σT (fun i => D (emb i))} {S : Prog σT (fun i => D (emb i))}
    (h : DerivTot A S B) :
    DerivTot (A.embFrame R hR) (S.onReg emb) (B.embFrame R hR) := by
  induction h generalizing R with
  | skip A => exact DerivTot.skip _
  | assign f A => exact DerivTot.assign (D := D) f (A.embFrame R hR)
  | initProg S A =>
      rw [Assn.embFrame_initPre (R := R) (hR := hR) emb A S]
      exact DerivTot.initProg _ _
  | unitary r U A =>
      rw [Assn.embFrame_unitaryPre (R := R) (hR := hR) emb A r U]
      exact DerivTot.unitary (D := D) (fun σ j => emb (r σ j)) U (A.embFrame R hR)
  | measure r M upd A =>
      rw [Assn.embFrame_measurePre (R := R) (hR := hR) emb A r M upd]
      exact DerivTot.measure (D := D) (fun σ j => emb (r σ j)) M upd (A.embFrame R hR)
  | seq h₁ h₂ ih₁ ih₂ => exact DerivTot.seq (ih₁ (R := R) (hR := hR)) (ih₂ (R := R) (hR := hR))
  | cond h₁ h₀ ih₁ ih₀ =>
      rw [Assn.embFrame_guard]
      exact DerivTot.cond (ih₁ (R := R) (hR := hR)) (ih₀ (R := R) (hR := hR))
  | whileLoop t hb ih =>
      rw [Assn.embFrame_mandNot]
      refine DerivTot.whileLoop t fun n => ?_
      have h' := ih n (R := R) (hR := hR)
      rw [Assn.embFrame_mask, Assn.embFrame_mand, Assn.embFrame_mask] at h'
      exact h'
  | whileLoopSource t hbound hInv hRank ihInv ihRank =>
      rw [Assn.embFrame_mandNot, Assn.embFrame_mask]
      refine DerivTot.whileLoopSource t hbound ?_ ?_
      · simpa only [Assn.embFrame_mand, Assn.embFrame_mask] using ihInv (R := R) (hR := hR)
      · intro z
        simpa only [Assn.embFrame_mask, Assn.embFrame_one_one] using
          ihRank z (R := 1) (hR := isEffect_one)
  | conseq hle h hle' ih =>
      exact DerivTot.conseq (Assn.embFrame_mono hle)
        (ih (R := R) (hR := hR)) (Assn.embFrame_mono hle')

end FrameRule

/-! ## §6. Store transport along a lens -/

section StorePull

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT σT' : Type*}

/-- Precompose an assertion family with a store read (the heterogeneous
`Assn.comp`). -/
def Assn.pull (g : σT' → σT) (A : Assn σT D) : Assn σT' D :=
  ⟨fun σ' => A.op (g σ'), fun σ' => A.isEffect (g σ')⟩

/-- `pull` is monotone (the (R-Conseq) transport). -/
theorem Assn.pull_mono (g : σT' → σT) {A B : Assn σT D} (h : A ≤ B) :
    A.pull g ≤ B.pull g := fun σ' => h (g σ')

@[simp]
theorem Assn.pull_op (g : σT' → σT) (A : Assn σT D) (σ' : σT') :
    (A.pull g).op σ' = A.op (g σ') := rfl

/-- **The derived store-transport rule** — a triple transports along
`Prog.mapStore` for any lawful lens (`get ∘ put = id`, the hypothesis the
counted-while pullback also takes), assertions precomposing with `l.get`.
Proved by induction on the derivation. -/
theorem DerivTot.mapStore_pull (l : StoreLens σT' σT)
    (hgp : ∀ σ' σ, l.get (l.put σ' σ) = σ)
    {A B : Assn σT D} {P : Prog σT D} (h : DerivTot A P B) :
    DerivTot (A.pull l.get) (P.mapStore l) (B.pull l.get) := by
  induction h with
  | skip A => exact DerivTot.skip _
  | assign f A =>
      have heq : (A.comp f).pull l.get
          = (A.pull l.get).comp fun σ' => l.put σ' (f (l.get σ')) :=
        Assn.ext (funext fun σ' => by
          rw [Assn.pull_op, Assn.comp_op, Assn.comp_op, Assn.pull_op, hgp])
      rw [heq]
      exact DerivTot.assign (D := D) (fun σ' => l.put σ' (f (l.get σ'))) (A.pull l.get)
  | initProg S A =>
      exact DerivTot.initProg (D := D) (fun σ' => S (l.get σ')) (A.pull l.get)
  | unitary r U A =>
      have heq : (A.unitaryPre r U).pull l.get
          = (A.pull l.get).unitaryPre (fun σ' => r (l.get σ'))
              fun σ' => U (l.get σ') := by
        refine Assn.ext (funext fun σ' => ?_)
        by_cases hi : Function.Injective (r (l.get σ'))
        · rw [Assn.pull_op, Assn.unitaryPre_op_of_dist A r U hi,
            Assn.unitaryPre_op_of_dist (A.pull l.get) (fun σ' => r (l.get σ'))
              (fun σ' => U (l.get σ')) (σ := σ') hi, Assn.pull_op]
        · rw [Assn.pull_op, Assn.unitaryPre_op_of_not_dist A r U hi,
            Assn.unitaryPre_op_of_not_dist (A.pull l.get) (fun σ' => r (l.get σ'))
              (fun σ' => U (l.get σ')) (σ := σ') hi]
      rw [heq]
      exact DerivTot.unitary (D := D) (fun σ' => r (l.get σ'))
        (fun σ' => U (l.get σ')) (A.pull l.get)
  | measure r M upd A =>
      have heq : (A.measurePre r M upd).pull l.get
          = (A.pull l.get).measurePre (fun σ' => r (l.get σ'))
              (fun σ' => M (l.get σ')) fun i σ' => l.put σ' (upd i (l.get σ')) := by
        refine Assn.ext (funext fun σ' => ?_)
        by_cases hi : Function.Injective (r (l.get σ'))
        · rw [Assn.pull_op, Assn.measurePre_op_of_dist A r M upd hi,
            Assn.measurePre_op_of_dist (A.pull l.get) (fun σ' => r (l.get σ'))
              (fun σ' => M (l.get σ')) (fun i σ' => l.put σ' (upd i (l.get σ')))
              (σ := σ') hi]
          exact Finset.sum_congr rfl fun i _ => by rw [Assn.pull_op, hgp]
        · rw [Assn.pull_op, Assn.measurePre_op_of_not_dist A r M upd hi,
            Assn.measurePre_op_of_not_dist (A.pull l.get) (fun σ' => r (l.get σ'))
              (fun σ' => M (l.get σ')) (fun i σ' => l.put σ' (upd i (l.get σ')))
              (σ := σ') hi]
      rw [heq]
      exact DerivTot.measure (D := D) (fun σ' => r (l.get σ')) (fun σ' => M (l.get σ'))
        (fun i σ' => l.put σ' (upd i (l.get σ'))) (A.pull l.get)
  | seq h₁ h₂ ih₁ ih₂ => exact DerivTot.seq ih₁ ih₂
  | cond h₁ h₀ ih₁ ih₀ => exact DerivTot.cond ih₁ ih₀
  | whileLoop t hb ih =>
      exact DerivTot.whileLoop (fun σ' => t (l.get σ')) fun n => ih n
  | @whileLoopSource b A φ P t hbound hInv hRank ihInv ihRank =>
      exact DerivTot.whileLoopSource (A := A.pull l.get) (b := fun σ => b (l.get σ))
        (fun σ' => t (l.get σ'))
        (fun σ' hφ => hbound (l.get σ') hφ) ihInv ihRank
  | conseq hle h hle' ih =>
      exact DerivTot.conseq (Assn.pull_mono l.get hle) ih (Assn.pull_mono l.get hle')

end StorePull

end Qhl
