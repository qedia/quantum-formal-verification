import Qhl.Dirac.Ring
import Qhl.Dirac.Unary

/-!
# Big operators on Dirac expressions and the bridge to layer 1

Mirror of `CoqQ/src/dirac/dirac.v:1113-1123,1999-2015` (D-8) and
`2156-2161` (D-9); spec 03 §3.

* D-8 sum-pushing through the constructors: `ofBlock_sum`, `ket_sum`,
  `bra_sum`, `num_sum` (CoqQ `lind_sum`/`ketd_sum`/`brad_sum`,
  `dirac.v:1113-1123`)
* D-8 unaries over big tensors: `adj_prod`, `conj_prod`, `transpose_prod`
  (CoqQ `tends_adj`/`tends_conj`/`tends_tr`, `dirac.v:1999-2015`); no swap
  anywhere since `⊗ᴰ` is commutative
* D-9 bridges to layer 1 — **unconditional**, no disjointness:
  `prod_ket : ∏ j, ∣u j⟩ᴰ = ∣tenvFamily D f u⟩ᴰ` (CoqQ `tenvm_correct:2156`)
  and `prod_ofBlock : ∏ j, ⌈φ j⌉ᴰ = ⌈tenfFamily D φ⌉ᴰ`
  (CoqQ `tenfm_correct:2161`), plus the cast absorptions `ket_castH`,
  `ket_deltav_default` they rest on

CoqQ's dffun-distribution lemmas (`tendA_distr_*`, `dirac.v:1126-1226`) are
deliberately **not** ported: with D-4 the big tensor is `Finset.prod`, so
mathlib's `Finset.prod_sum`/`Finset.prod_univ_sum` already provide that shape
(spec 03 §3; revisit only if M5 needs specific instances).
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L] {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] {S T : Finset L}

namespace Dirac

/-! ## D-8: sum-pushing through the constructors (CoqQ `dirac.v:1113-1123`) -/

/-- `ofBlock` commutes with finite sums. CoqQ `lind_sum` (`dirac.v:1113`). -/
theorem ofBlock_sum {ι : Type*} (s : Finset ι) (f : ι → LinM D S T) :
    (⌈∑ i ∈ s, f i⌉ᴰ : Dirac D) = ∑ i ∈ s, ⌈f i⌉ᴰ := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, ofBlock_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ofBlock_add, ih]

/-- `ket` commutes with finite sums. CoqQ `ketd_sum` (`dirac.v:1117`). -/
theorem ket_sum {ι : Type*} (s : Finset ι) (v : ι → HS D S) :
    (∣∑ i ∈ s, v i⟩ᴰ : Dirac D) = ∑ i ∈ s, ∣v i⟩ᴰ := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, ket_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ket_add, ih]

/-- `bra` commutes with finite sums (it is additive, only homogeneity
conjugates). CoqQ `brad_sum` (`dirac.v:1121`). -/
theorem bra_sum {ι : Type*} (s : Finset ι) (v : ι → HS D S) :
    (⟨∑ i ∈ s, v i∣ᴰ : Dirac D) = ∑ i ∈ s, ⟨v i∣ᴰ := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, bra_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, bra_add, ih]

/-- `num` commutes with finite sums. CoqQ `dirac.v:1113-1123`-area. -/
theorem num_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) :
    num D (∑ i ∈ s, c i) = ∑ i ∈ s, num D (c i) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, num_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, num_add, ih]

/-- `num` turns products of scalars into big tensors (`∏` *is* the big tensor
on `Dirac`, D-4). CoqQ `numdBT` (`dirac.v:2093`-area); via
`algebraMap_eq_num` + `map_prod`. -/
theorem num_prod {ι : Type*} (s : Finset ι) (c : ι → ℂ) :
    num D (∏ i ∈ s, c i) = ∏ i ∈ s, num D (c i) := by
  rw [← algebraMap_eq_num, map_prod]
  exact Finset.prod_congr rfl fun i _ => algebraMap_eq_num (c i)

/-! ## D-8: unaries over big tensors (CoqQ `dirac.v:1999-2015`)

No operand swap anywhere: `⊗ᴰ` is commutative, so the anti-multiplicativity
of `†ᴰ` is invisible on tensors (cf. `adj_tensor`). Like their binary
versions these are deliberately not `simp` (they would fight `ring`-normal
forms). -/

/-- `†ᴰ` distributes over big tensors. CoqQ `tends_adj` (`dirac.v:1999`). -/
theorem adj_prod {ι : Type*} (s : Finset ι) (d : ι → Dirac D) :
    (∏ i ∈ s, d i)†ᴰ = ∏ i ∈ s, (d i)†ᴰ := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, one_def, adj_num, star_one]
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons, mul_def, mul_def, adj_tensor, ih]

/-- `ᶜᴰ` distributes over big tensors. CoqQ `tends_conj` (`dirac.v:2007`). -/
theorem conj_prod {ι : Type*} (s : Finset ι) (d : ι → Dirac D) :
    (∏ i ∈ s, d i)ᶜᴰ = ∏ i ∈ s, (d i)ᶜᴰ := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, one_def, conj_num, star_one]
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons, mul_def, mul_def, conj_tensor, ih]

/-- `ᵀᴰ` distributes over big tensors. CoqQ `tends_tr` (`dirac.v:2015`). -/
theorem transpose_prod {ι : Type*} (s : Finset ι) (d : ι → Dirac D) :
    (∏ i ∈ s, d i)ᵀᴰ = ∏ i ∈ s, (d i)ᵀᴰ := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, one_def, transpose_num]
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons, mul_def, mul_def,
        transpose_tensor, ih]

/-! ## D-9: the bridge to layer 1 (CoqQ `tenvm_correct:2156`,
`tenfm_correct:2161`) — no side conditions -/

/-- Cast absorption: `ket` swallows `castH` (the ket companion of
`ofBlock_castF`; CoqQ handles this via `casths` conversions inside
`tenvm_correct`, `dirac.v:2156`). -/
@[simp, cast_simps, dirac_simps]
theorem ket_castH (h : S = T) (v : HS D S) :
    (∣castH D h v⟩ᴰ : Dirac D) = ∣v⟩ᴰ := by
  subst h; simp

/-- The empty-register basis ket is the unit scalar `1ᴰ` (base case of CoqQ
`tenvm_correct`, `dirac.v:2156`). -/
@[simp, dirac_simps]
theorem ket_deltav_default :
    (∣deltav D (default : QIdx D ∅)⟩ᴰ : Dirac D) = 1 := by
  rw [ket, toKetM_def, outerLM_deltav_default, one_def, num, toScalarM_one]

/-- Head-peel of `univ.biUnion` over `Fin (n + 1)` (the label-set side of
`tenvFamily_succ`/`tenfFamily_succ`). -/
private theorem biUnion_succ {n : ℕ} (f : Fin (n + 1) → Finset L) :
    f 0 ∪ univ.biUnion (fun j : Fin n => f j.succ) = univ.biUnion f := by
  ext x
  simp only [mem_union, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro (hx | ⟨j, hj⟩)
    · exact ⟨0, hx⟩
    · exact ⟨j.succ, hj⟩
  · rintro ⟨j, hj⟩
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
    · exact Or.inl hj
    · exact Or.inr ⟨i, hj⟩

/-- `univ.biUnion` is invariant under reindexing by an equivalence. -/
private theorem biUnion_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (f : ι → Finset L) :
    univ.biUnion f = univ.biUnion fun j => f (e j) := by
  ext x
  simp only [mem_biUnion, mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => ⟨e.symm i, by simpa using hi⟩, fun ⟨j, hj⟩ => ⟨e j, hj⟩⟩

/-- `Fin` case of `prod_ket`, by induction on `n` (head-peel via
`tenvFamily_succ`). -/
private theorem prod_ket_fin {n : ℕ} (f : Fin n → Finset L)
    (u : ∀ j, HS D (f j)) :
    ∏ j, (∣u j⟩ᴰ : Dirac D) = ∣tenvFamily D f u⟩ᴰ := by
  induction n with
  | zero =>
      rw [Fin.prod_univ_zero, tenvFamily_isEmpty D f u (by simp), ket_castH,
        ket_deltav_default]
  | succ n ih =>
      rw [Fin.prod_univ_succ, ih, mul_def, ket_tensor_ket,
        ← tenvFamily_succ D f u (biUnion_succ f), ket_castH]

/-- `Fin` case of `prod_ofBlock`, by induction on `n` (head-peel via
`tenfFamily_succ`). -/
private theorem prod_ofBlock_fin {n : ℕ} {Sf Tf : Fin n → Finset L}
    (φ : ∀ j, LinM D (Sf j) (Tf j)) :
    ∏ j, (⌈φ j⌉ᴰ : Dirac D) = ⌈tenfFamily D φ⌉ᴰ := by
  induction n with
  | zero =>
      rw [Fin.prod_univ_zero, tenfFamily_isEmpty D φ (by simp) (by simp),
        ofBlock_castF, one_def, num, toScalarM_one]
  | succ n ih =>
      rw [Fin.prod_univ_succ, ih, mul_def, ofBlock_tensor,
        ← tenfFamily_succ D φ (biUnion_succ Sf) (biUnion_succ Tf), ofBlock_castF]

/-- **D-9, ket version**: the big tensor of labelled kets is the ket of the
layer-1 family tensor — *unconditionally*, no disjointness. CoqQ
`tenvm_correct` (`dirac.v:2156`). -/
@[simp, dirac_simps]
theorem prod_ket {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Finset L)
    (u : ∀ j, HS D (f j)) :
    ∏ j, (∣u j⟩ᴰ : Dirac D) = ∣tenvFamily D f u⟩ᴰ := by
  rw [← Equiv.prod_comp (Fintype.equivFin ι).symm fun j => (∣u j⟩ᴰ : Dirac D),
    prod_ket_fin,
    tenvFamily_reindex D f (Fintype.equivFin ι).symm u
      (biUnion_reindex (Fintype.equivFin ι).symm f),
    ket_castH]

/-- **D-9, bra version**: the big tensor of labelled bras is the bra of the
layer-1 family tensor — *unconditionally* (adjoint of `prod_ket`; CoqQ
`tenvm_correct`-dual, `dirac.v:2156`-area). -/
@[simp, dirac_simps]
theorem prod_bra {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Finset L)
    (u : ∀ j, HS D (f j)) :
    ∏ j, (⟨u j∣ᴰ : Dirac D) = ⟨tenvFamily D f u∣ᴰ := by
  simp only [← adj_ket]
  rw [← adj_prod, prod_ket]

/-- **D-9, operator version**: the big tensor of labelled block operators is
the block of the layer-1 family operator tensor — *unconditionally*, no
disjointness. CoqQ `tenfm_correct` (`dirac.v:2161`). -/
@[simp, dirac_simps]
theorem prod_ofBlock {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Sf Tf : ι → Finset L} (φ : ∀ j, LinM D (Sf j) (Tf j)) :
    ∏ j, (⌈φ j⌉ᴰ : Dirac D) = ⌈tenfFamily D φ⌉ᴰ := by
  rw [← Equiv.prod_comp (Fintype.equivFin ι).symm fun j => (⌈φ j⌉ᴰ : Dirac D),
    prod_ofBlock_fin,
    tenfFamily_reindex D (Fintype.equivFin ι).symm φ
      (biUnion_reindex (Fintype.equivFin ι).symm Sf)
      (biUnion_reindex (Fintype.equivFin ι).symm Tf),
    ofBlock_castF]

end Dirac

end Qhl
