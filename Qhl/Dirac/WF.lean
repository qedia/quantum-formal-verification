import Qhl.Dirac.BigOps

/-!
# Well-formedness of Dirac expressions: the `WFAt` predicate and its table

Mirror of `CoqQ/src/dirac/dirac.v:1230-1691`, unconditional part (spec 03 §5,
subgoal D-10).

* `Dirac.WFAt S T d` — `d` is concentrated on the single block `(S, T)`
  (CoqQ `wfdirac_axiom:1230`); abbreviations `IsKetOn`/`IsBraOn`/`IsSqOn`
  (CoqQ `'Ket_S`/`'Bra_S`/`'D_S`)
* structure theorems: `WFAt.eq`/`WFAt.eq'` (CoqQ `wfdiracE:1352`, the main
  block-rewriting device of the labelled laws in `Qhl.Dirac.Laws`),
  `WFAt.apply_of_ne_left/right`, canonical forms `IsKetOn.eq_ket`
  (CoqQ `ketdiracE:1356`), `IsBraOn.eq_bra`, `IsSqOn.eq_ofBlock`, uniqueness
  of the support `WFAt.support_unique` (CoqQ `wfdirac_eqP:1392`)
* the wf table (CoqQ `*_wf:1438-1658`): constructors `wf_ofBlock`/`wf_ket`/
  `wf_bra`/`wf_num`/`wf_one`/`wf_zero` (tagged `simp, wf_simps`); closure
  under the module operations (`WFAt.add/smul/neg/sub/sum`), the unaries
  (`WFAt.adj/conj/transpose`), the products (`WFAt.comp/tensor/dot/prod`);
  retyping `WFAt.cast`

The closure lemmas are rule-shaped (their conclusion mentions fresh label
sets), so they are deliberately *not* simp; use them namespace-dot style,
`hd₁.add hd₂`, `hd₁.dot hd₂`, `h.cast e₁ e₂`.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L] {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] {S T W S' T' : Finset L}

namespace Dirac

/-- Well-formedness at the block `(S, T)`: the Dirac expression `d` is its own
`(S, T)`-block, hence `0` everywhere else. CoqQ: `wfdirac_axiom`
(`dirac.v:1230`). -/
def WFAt (S T : Finset L) (d : Dirac D) : Prop :=
  (⌈d S T⌉ᴰ : Dirac D) = d

/-- A labelled ket on `S` (block `(∅, S)`). CoqQ: `'Ket_S` (`dirac.v:1230-1350`). -/
abbrev IsKetOn (S : Finset L) (d : Dirac D) : Prop := WFAt ∅ S d

/-- A labelled bra on `S` (block `(S, ∅)`). CoqQ: `'Bra_S` (`dirac.v:1230-1350`). -/
abbrev IsBraOn (S : Finset L) (d : Dirac D) : Prop := WFAt S ∅ d

/-- A square labelled operator on `S` (block `(S, S)`). CoqQ: `'D_S`
(`dirac.v:1230-1350`). -/
abbrev IsSqOn (S : Finset L) (d : Dirac D) : Prop := WFAt S S d

/-! ## Structure theorems (CoqQ `wfdiracE:1352`, `ketdiracE:1356`,
`wfdirac_eqP:1392`) -/

/-- A wf expression *is* its home block. CoqQ: `wfdiracE` (`dirac.v:1352`). -/
theorem WFAt.eq {d : Dirac D} (h : WFAt S T d) : (⌈d S T⌉ᴰ : Dirac D) = d := h

/-- `WFAt.eq`, oriented to rewrite `d` *into* block form — the main proof
device for the labelled laws (spec 03 §4). CoqQ: `wfdiracE` (`dirac.v:1352`). -/
theorem WFAt.eq' {d : Dirac D} (h : WFAt S T d) : d = (⌈d S T⌉ᴰ : Dirac D) :=
  h.symm

/-- A wf expression vanishes at blocks with the wrong source. CoqQ:
`wfdirac_eqP`-adjacent (`dirac.v:1392`-area). -/
theorem WFAt.apply_of_ne_left {d : Dirac D} (h : WFAt S T d) (hne : S' ≠ S) :
    d S' T' = 0 := by
  rw [← h.eq]
  exact ofBlock_apply_of_ne_left _ hne

/-- A wf expression vanishes at blocks with the wrong target. CoqQ:
`wfdirac_eqP`-adjacent (`dirac.v:1392`-area). -/
theorem WFAt.apply_of_ne_right {d : Dirac D} (h : WFAt S T d) (hne : T' ≠ T) :
    d S' T' = 0 := by
  rw [← h.eq]
  exact ofBlock_apply_of_ne_right _ hne

/-- Canonical form of a labelled ket. CoqQ: `ketdiracE` (`dirac.v:1356`). -/
theorem IsKetOn.eq_ket {d : Dirac D} (h : IsKetOn S d) : d = ∣toKet S d⟩ᴰ := by
  rw [ket, toKet, toKetM_ofKetM]
  exact h.eq'

/-- Canonical form of a labelled bra. CoqQ: `bradiracE` (`dirac.v:1356`-area). -/
theorem IsBraOn.eq_bra {d : Dirac D} (h : IsBraOn S d) : d = ⟨toBra S d∣ᴰ := by
  rw [bra, toBra, toBraM_ofBraM]
  exact h.eq'

/-- Canonical form of a square labelled operator. CoqQ: `wfdiracE` at `'D_S`
(`dirac.v:1352`-area). -/
theorem IsSqOn.eq_ofBlock {d : Dirac D} (h : IsSqOn S d) :
    d = (⌈d S S⌉ᴰ : Dirac D) :=
  h.eq'

/-- The support of a nonzero wf expression is unique. CoqQ: `wfdirac_eqP`
(`dirac.v:1392`). -/
theorem WFAt.support_unique {d : Dirac D} (h₁ : WFAt S T d)
    (h₂ : WFAt S' T' d) (hd : d ≠ 0) : S = S' ∧ T = T' := by
  constructor <;> by_contra hne
  · exact hd (by rw [← h₁.eq, h₂.apply_of_ne_left hne, ofBlock_zero])
  · exact hd (by rw [← h₁.eq, h₂.apply_of_ne_right hne, ofBlock_zero])

/-! ## The wf table, constructors (CoqQ `*_wf`, `dirac.v:1438-1469`) -/

/-- A single block is wf at its home block. CoqQ: `lind_wf` (`dirac.v:1469`). -/
@[simp, wf_simps]
theorem wf_ofBlock (f : LinM D S T) : WFAt S T (⌈f⌉ᴰ : Dirac D) :=
  congrArg ofBlock (ofBlock_apply_self f)

/-- Kets are wf at `(∅, S)`. CoqQ: `ketd_wf` (`dirac.v:1448`). -/
@[simp, wf_simps]
theorem wf_ket (v : HS D S) : WFAt ∅ S (∣v⟩ᴰ : Dirac D) :=
  wf_ofBlock _

/-- Bras are wf at `(S, ∅)`. CoqQ: `brad_wf` (`dirac.v:1452`). -/
@[simp, wf_simps]
theorem wf_bra (v : HS D S) : WFAt S ∅ (⟨v∣ᴰ : Dirac D) :=
  wf_ofBlock _

/-- Scalars are wf at `(∅, ∅)`. CoqQ: `numd_wf` (`dirac.v:1456`). -/
@[simp, wf_simps]
theorem wf_num (c : ℂ) : WFAt ∅ ∅ (num D c) :=
  wf_ofBlock _

/-- Identities are wf at `(S, S)`. CoqQ: `dirac.v:1448-1469`-area. -/
@[simp, wf_simps]
theorem wf_one : WFAt S S (𝟙ᴰ S : Dirac D) :=
  wf_ofBlock _

/-- `0` is wf at every block. CoqQ: `dirac.v:1476-1499`-area. -/
@[simp, wf_simps]
theorem wf_zero : WFAt S T (0 : Dirac D) := by
  change (⌈(0 : Dirac D) S T⌉ᴰ : Dirac D) = 0
  rw [zero_apply, ofBlock_zero]

/-! ## The wf table, closure under the module operations
(CoqQ `dirac.v:1476-1499`, `sumd_wf:1611`) -/

/-- CoqQ: `addd_wf` (`dirac.v:1476-1499`). -/
theorem WFAt.add {d e : Dirac D} (h₁ : WFAt S T d) (h₂ : WFAt S T e) :
    WFAt S T (d + e) := by
  change (⌈(d + e) S T⌉ᴰ : Dirac D) = d + e
  rw [add_apply, ofBlock_add, h₁.eq, h₂.eq]

/-- CoqQ: `scaled_wf` (`dirac.v:1476-1499`). -/
theorem WFAt.smul {d : Dirac D} (c : ℂ) (h : WFAt S T d) : WFAt S T (c • d) := by
  change (⌈(c • d) S T⌉ᴰ : Dirac D) = c • d
  rw [smul_apply, ofBlock_smul, h.eq]

/-- CoqQ: `oppd_wf` (`dirac.v:1476-1499`). -/
theorem WFAt.neg {d : Dirac D} (h : WFAt S T d) : WFAt S T (-d) := by
  change (⌈(-d) S T⌉ᴰ : Dirac D) = -d
  rw [neg_apply, ofBlock_neg, h.eq]

/-- CoqQ: `dirac.v:1476-1499`-area. -/
theorem WFAt.sub {d e : Dirac D} (h₁ : WFAt S T d) (h₂ : WFAt S T e) :
    WFAt S T (d - e) := by
  change (⌈(d - e) S T⌉ᴰ : Dirac D) = d - e
  rw [sub_apply, ofBlock_sub, h₁.eq, h₂.eq]

/-- CoqQ: `sumd_wf` (`dirac.v:1611`). -/
theorem WFAt.sum {ι : Type*} {s : Finset ι} {d : ι → Dirac D}
    (h : ∀ i ∈ s, WFAt S T (d i)) : WFAt S T (∑ i ∈ s, d i) := by
  change (⌈(∑ i ∈ s, d i) S T⌉ᴰ : Dirac D) = ∑ i ∈ s, d i
  rw [sum_apply, ofBlock_sum]
  exact Finset.sum_congr rfl fun i hi => (h i hi).eq

/-! ## The wf table, unaries (CoqQ `dirac.v:1501-1520`) -/

/-- `†ᴰ` transposes the support. CoqQ: `adjd_wf` (`dirac.v:1501-1520`). -/
theorem WFAt.adj {d : Dirac D} (h : WFAt S T d) : WFAt T S (d†ᴰ) := by
  rw [← h.eq, adj_ofBlock]
  exact wf_ofBlock _

/-- `ᶜᴰ` keeps the support. CoqQ: `conjd_wf` (`dirac.v:1501-1520`). -/
theorem WFAt.conj {d : Dirac D} (h : WFAt S T d) : WFAt S T (dᶜᴰ) := by
  rw [← h.eq, conj_ofBlock]
  exact wf_ofBlock _

/-- `ᵀᴰ` transposes the support. CoqQ: `trd_wf` (`dirac.v:1501-1520`). -/
theorem WFAt.transpose {d : Dirac D} (h : WFAt S T d) : WFAt T S (dᵀᴰ) := by
  rw [← h.eq, transpose_ofBlock]
  exact wf_ofBlock _

/-! ## The wf table, products (CoqQ `muld_wf:1522`, `tend_wf:1534`,
`dotd_wf:1552`, `tends_wf:1573`) -/

/-- CoqQ: `muld_wf` (`dirac.v:1522`). -/
theorem WFAt.comp {d₁ d₂ : Dirac D} (h₁ : WFAt S T d₁) (h₂ : WFAt W S d₂) :
    WFAt W T (d₁ ∘ᴰ d₂) := by
  rw [← h₁.eq, ← h₂.eq, ofBlock_comp]
  exact wf_ofBlock _

/-- CoqQ: `tend_wf` (`dirac.v:1534`). -/
theorem WFAt.tensor {d₁ d₂ : Dirac D} (h₁ : WFAt S T d₁) (h₂ : WFAt S' T' d₂) :
    WFAt (S ∪ S') (T ∪ T') (d₁ ⊗ᴰ d₂) := by
  rw [← h₁.eq, ← h₂.eq, ofBlock_tensor]
  exact wf_ofBlock _

/-- CoqQ: `dotd_wf` (`dirac.v:1552`). -/
theorem WFAt.dot {d₁ d₂ : Dirac D} (h₁ : WFAt S T d₁) (h₂ : WFAt S' T' d₂) :
    WFAt (S' ∪ (S \ T')) (T ∪ (T' \ S)) (d₁ ·ᴰ d₂) := by
  rw [← h₁.eq, ← h₂.eq, ofBlock_dot]
  exact wf_ofBlock _

/-- CoqQ: `tends_wf` (`dirac.v:1573`). -/
theorem WFAt.prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Sf Tf : ι → Finset L} {d : ι → Dirac D}
    (h : ∀ j, WFAt (Sf j) (Tf j) (d j)) :
    WFAt (univ.biUnion Sf) (univ.biUnion Tf) (∏ j, d j) := by
  rw [show ∏ j, d j = ∏ j, (⌈(d j) (Sf j) (Tf j)⌉ᴰ : Dirac D) from
    Finset.prod_congr rfl fun j _ => ((h j).eq).symm, prod_ofBlock]
  exact wf_ofBlock _

/-- Retyping along equalities of label sets (ubiquitous downstream; CoqQ
handles this with `castlf`/canonical retyping, `dirac.v:1230-1691`). -/
theorem WFAt.cast (e₁ : S = S') (e₂ : T = T') {d : Dirac D} (h : WFAt S T d) :
    WFAt S' T' d :=
  e₁ ▸ e₂ ▸ h

end Dirac

end Qhl
