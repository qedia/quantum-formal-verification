import Qhl.HSpace.Basic

/-!
# Labelled Hilbert spaces: index calculus

Mirror of the classical-state index calculus of `CoqQ/src/dirac/hstensor.v:466-941`
(spec 02 §2, subgoals H-4, H-5, H-7, H-8).

Since `QIdx D S` is an abbrev for the Pi type `∀ i : ↥S, D i`, dot notation
(`k.res`) does not fire; the call pattern is prefix application with `D`
explicit, matching `Qhl.HSpace.Basic`:

* `QIdx.res D h k` — restriction along `h : S ⊆ U` (CoqQ `idxR`/`idxSl`/`idxSr`)
* `QIdx.merge D k l` — left-biased merge (CoqQ `idxU`)
* `QIdx.cast D h` — reindexing equivalence along `h : S = T` (CoqQ `castidx`)
* `QIdx.pack D f v` — flattening of a family of states (CoqQ `packidx`)
* `splitEquiv D hd : QIdx D (S ∪ T) ≃ QIdx D S × QIdx D T`
* `packEquiv D f hd : QIdx D (univ.biUnion f) ≃ ∀ j, QIdx D (f j)`
  (CoqQ `flatidx`/`packidx`)

All maps are total; disjointness appears only in the round-trip laws.
-/

namespace Qhl

open Finset

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S T U : Finset L}

namespace QIdx

/-- Restriction of a classical state along `S ⊆ U`. CoqQ `idxR`/`idxSl`/`idxSr`
(`hstensor.v:466-690`). -/
def res (h : S ⊆ U) (k : QIdx D U) : QIdx D S := fun i => k ⟨i, h i.2⟩

/-- Left-biased merge of classical states. CoqQ `idxU` (`hstensor.v:700`). -/
def merge (k : QIdx D S) (l : QIdx D T) : QIdx D (S ∪ T) := fun i =>
  if h : (i : L) ∈ S then k ⟨i, h⟩ else l ⟨i, (Finset.mem_union.1 i.2).resolve_left h⟩

/-- Reindexing of classical states along an equality of label sets; only the
membership proofs are transported, never the space (Decision H1). CoqQ
`castidx` (`hstensor.v:292`). -/
def cast (h : S = T) : QIdx D S ≃ QIdx D T where
  toFun k i := k ⟨i, h.symm ▸ i.2⟩
  invFun k i := k ⟨i, h ▸ i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## H-4: computation laws for `res`/`merge` -/

/-- CoqQ `idxSUl` (`hstensor.v:813`). -/
@[simp, HS_simps]
theorem res_merge_left (h : S ⊆ S ∪ T) (k : QIdx D S) (l : QIdx D T) :
    res D h (merge D k l) = k :=
  funext fun i => dif_pos i.2

/-- CoqQ `idxSUr` (`hstensor.v:821`). -/
@[simp, HS_simps]
theorem res_merge_right (hd : Disjoint S T) (h : T ⊆ S ∪ T) (k : QIdx D S)
    (l : QIdx D T) : res D h (merge D k l) = l :=
  funext fun i => dif_neg fun hS => Finset.disjoint_left.1 hd hS i.2

/-- CoqQ `idxUS` (`hstensor.v:806`). -/
@[simp, HS_simps]
theorem merge_res (h₁ : S ⊆ S ∪ T) (h₂ : T ⊆ S ∪ T) (k : QIdx D (S ∪ T)) :
    merge D (res D h₁ k) (res D h₂ k) = k :=
  funext fun i => by
    by_cases hS : (i : L) ∈ S
    · exact dif_pos hS
    · exact dif_neg hS

/-- CoqQ `idxRA` (`hstensor.v:840`). -/
@[simp, HS_simps]
theorem res_res (h₁ : S ⊆ T) (h₂ : T ⊆ U) (k : QIdx D U) :
    res D h₁ (res D h₂ k) = res D (h₁.trans h₂) k :=
  rfl

/-! ## H-8: cast laws

`cast_rfl` is stated for an arbitrary proof `h : S = S`, so by proof
irrelevance it collapses any self-cast, e.g. the `h.trans h.symm` produced by
`cast_cast`. -/

/-- CoqQ `castidx_id` (`hstensor.v:292-303`). -/
@[simp, cast_simps]
theorem cast_rfl (h : S = S) : cast D h = Equiv.refl (QIdx D S) :=
  Equiv.ext fun _ => rfl

/-- CoqQ `castidx_comp` (`hstensor.v:292-303`). -/
@[simp, cast_simps]
theorem cast_trans (h₁ : S = T) (h₂ : T = U) :
    (cast D h₁).trans (cast D h₂) = cast D (h₁.trans h₂) :=
  Equiv.ext fun _ => rfl

/-- Applied form of `cast_trans`. -/
@[simp, cast_simps]
theorem cast_cast (h₁ : S = T) (h₂ : T = U) (k : QIdx D S) :
    cast D h₂ (cast D h₁ k) = cast D (h₁.trans h₂) k :=
  rfl

/-- CoqQ `castidx_K` (`hstensor.v:292-303`). -/
@[simp, cast_simps]
theorem cast_symm (h : S = T) : (cast D h).symm = cast D h.symm :=
  Equiv.ext fun _ => rfl

/-! ## H-7: flattening a finite family (CoqQ `flatidx`/`packidx`) -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Finset L)

/-- Flatten a family of classical states into one on the union; the label is
looked up in an arbitrary member of the family containing it (total, no
disjointness required). CoqQ `packidx` (`hstensor.v:473-564`). -/
noncomputable def pack (v : ∀ j, QIdx D (f j)) : QIdx D (univ.biUnion f) := fun i =>
  have h : ∃ j, (i : L) ∈ f j := (mem_biUnion.1 i.2).imp fun _ hj => hj.2
  v h.choose ⟨i, h.choose_spec⟩

/-- Round trip: flattening the family of restrictions recovers the state.
CoqQ `flatidxK` (`hstensor.v:473-564`). -/
@[simp, HS_simps]
theorem pack_res (k : QIdx D (univ.biUnion f)) :
    pack D f (fun j => res D (subset_biUnion_of_mem f (mem_univ j)) k) = k :=
  rfl

/-- On a pairwise-disjoint family, `pack` looks up the unique member of the
family containing the label. -/
theorem pack_apply (hd : Pairwise (Function.onFun Disjoint f))
    (v : ∀ j, QIdx D (f j)) {j : ι} (i : ↥(univ.biUnion f))
    (hij : (i : L) ∈ f j) : pack D f v i = v j ⟨i, hij⟩ := by
  have h : ∃ j', (i : L) ∈ f j' := ⟨j, hij⟩
  have hc : h.choose = j :=
    hd.eq fun hdis => Finset.disjoint_left.1 hdis h.choose_spec hij
  subst hc
  rfl

/-- Round trip: restricting a flattened state recovers the component (needs
pairwise disjointness). CoqQ `packidxK` (`hstensor.v:473-564`). -/
@[simp, HS_simps]
theorem res_pack (hd : Pairwise (Function.onFun Disjoint f))
    (v : ∀ j, QIdx D (f j)) (j : ι) :
    res D (subset_biUnion_of_mem f (mem_univ j)) (pack D f v) = v j :=
  funext fun i =>
    pack_apply D f hd v ⟨i, subset_biUnion_of_mem f (mem_univ j) i.2⟩ i.2

end QIdx

/-! ## H-5: splitting a disjoint union -/

/-- Classical states on a disjoint union are pairs of classical states
(forward: two `QIdx.res`; inverse: `QIdx.merge`). Spec 02, H-5. -/
def splitEquiv (hd : Disjoint S T) : QIdx D (S ∪ T) ≃ QIdx D S × QIdx D T where
  toFun k := (QIdx.res D subset_union_left k, QIdx.res D subset_union_right k)
  invFun kl := QIdx.merge D kl.1 kl.2
  left_inv k := QIdx.merge_res D subset_union_left subset_union_right k
  right_inv := fun ⟨k, l⟩ => by simp [hd]

@[simp, HS_simps]
theorem splitEquiv_apply (hd : Disjoint S T) (k : QIdx D (S ∪ T)) :
    splitEquiv D hd k =
      (QIdx.res D subset_union_left k, QIdx.res D subset_union_right k) :=
  rfl

@[simp, HS_simps]
theorem splitEquiv_symm_apply (hd : Disjoint S T) (kl : QIdx D S × QIdx D T) :
    (splitEquiv D hd).symm kl = QIdx.merge D kl.1 kl.2 :=
  rfl

/-! ## H-7: packing a pairwise-disjoint family -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Finset L)

/-- Classical states on the union of a pairwise-disjoint family are tuples of
classical states (forward: `QIdx.res` at each member; inverse: `QIdx.pack`).
CoqQ `flatidx`/`packidx` (`hstensor.v:473-564`). -/
noncomputable def packEquiv (hd : Pairwise (Function.onFun Disjoint f)) :
    QIdx D (univ.biUnion f) ≃ ∀ j, QIdx D (f j) where
  toFun k j := QIdx.res D (subset_biUnion_of_mem f (mem_univ j)) k
  invFun := QIdx.pack D f
  left_inv _ := rfl
  right_inv v := funext fun j => QIdx.res_pack D f hd v j

@[simp, HS_simps]
theorem packEquiv_apply (hd : Pairwise (Function.onFun Disjoint f))
    (k : QIdx D (univ.biUnion f)) (j : ι) :
    packEquiv D f hd k j = QIdx.res D (subset_biUnion_of_mem f (mem_univ j)) k :=
  rfl

@[simp, HS_simps]
theorem packEquiv_symm_apply (hd : Pairwise (Function.onFun Disjoint f))
    (v : ∀ j, QIdx D (f j)) :
    (packEquiv D f hd).symm v = QIdx.pack D f v :=
  rfl

end Qhl
