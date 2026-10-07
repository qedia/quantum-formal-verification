import Qhl.Dirac.Constructors
import Qhl.HSpace.DotF

/-!
# Dirac products: composition, tensor, dot, adjoint, conjugate, transpose

Mirror of `CoqQ/src/dirac/dirac.v:237-260` (definitions), `398-593` and
`1845-1884` (D-5 correctness), `681-871` (D-6 bilinearity); spec 03 §3.

* `Dirac.comp` (`d₁ ∘ᴰ d₂`) — blockwise `∑ W, d₁ W T ∘ₗ d₂ S W`
  (CoqQ `muld:243`)
* `Dirac.tensor` (`d₁ ⊗ᴰ d₂`) — `∑` over all block pairs of
  `⌈tenf D (d₁ S₁ T₁) (d₂ S₂ T₂)⌉ᴰ` (CoqQ `tend:249`)
* `Dirac.dot` (`d₁ ·ᴰ d₂`) — same four-fold sum with `dotf`
  (CoqQ `dotd:246`)
* `Dirac.adj` (`d†ᴰ`), `Dirac.conj` (`dᶜᴰ`), `Dirac.transpose` (`dᵀᴰ`) —
  blockwise adjoint/`conjLM`/`transposeLM`, with the block transposed for
  `†ᴰ`/`ᵀᴰ` (CoqQ `adjd:241`, `conjd:237`, `trd:239`)
* D-5: the constructors are homomorphic — `ofBlock_comp`, `ofBlock_tensor`,
  `ofBlock_dot`, `adj_ofBlock`, `conj_ofBlock`, `transpose_ofBlock`,
  `ket_tensor_ket`, `bra_comp_ket`, `ket_comp_bra`, `ofBlock_dot_ket`
* D-6 (bilinearity part): `_add_left/right`, `_smul_left/right`,
  `_zero_left/right` for all three products; additivity and
  (conjugate-)homogeneity of `†ᴰ`/`ᶜᴰ`/`ᵀᴰ`

Sum collapses go through the helpers `sum_block_collapse` (one `ofBlock`
argument) and `sum_block_collapse₂` (two), which kill all off-support blocks
using the zero-absorption hypotheses.

Notation precedences: `⊗ᴰ` is `infixl:100` (like layer-1 `⊗ᶠ`/`⊗ᵥ`), `∘ᴰ` is
`infixr:80` (like `∘ₗ`), `·ᴰ` is `infixl:70` (binds weaker than both);
`†ᴰ`/`ᶜᴰ`/`ᵀᴰ` are `postfix:max`.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

variable {L : Type*} [Fintype L] [DecidableEq L] {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] {S T W S' T' : Finset L}

namespace Dirac

/-! ## The six operations (CoqQ `dirac.v:237-260`) -/

/-- Composition of Dirac expressions: blockwise, all middle label sets are
summed over. CoqQ: `muld` / `\o` (`dirac.v:243`). -/
def comp (d₁ d₂ : Dirac D) : Dirac D :=
  ofFun fun S T => ∑ W : Finset L, d₁ W T ∘ₗ d₂ S W

/-- Tensor of Dirac expressions: the sum of the operator tensors of all block
pairs, each placed at its home block. CoqQ: `tend` / `\ten` (`dirac.v:249`). -/
noncomputable def tensor (d₁ d₂ : Dirac D) : Dirac D :=
  ∑ S₁ : Finset L, ∑ T₁ : Finset L, ∑ S₂ : Finset L, ∑ T₂ : Finset L,
    ofBlock (tenf D (d₁ S₁ T₁) (d₂ S₂ T₂))

/-- Dot (general contraction) of Dirac expressions: the sum of the general
compositions `dotf` of all block pairs. CoqQ: `dotd` / `\cdot`
(`dirac.v:246`). -/
noncomputable def dot (d₁ d₂ : Dirac D) : Dirac D :=
  ∑ S₁ : Finset L, ∑ T₁ : Finset L, ∑ S₂ : Finset L, ∑ T₂ : Finset L,
    ofBlock (dotf D (d₁ S₁ T₁) (d₂ S₂ T₂))

/-- Adjoint of a Dirac expression: blockwise adjoint at the transposed block.
CoqQ: `adjd` (`dirac.v:241`). -/
noncomputable def adj (d : Dirac D) : Dirac D :=
  ofFun fun S T => LinearMap.adjoint (d T S)

/-- Conjugate of a Dirac expression: componentwise `conjLM`.
CoqQ: `conjd` (`dirac.v:237`). -/
def conj (d : Dirac D) : Dirac D :=
  ofFun fun S T => conjLM (d S T)

/-- Transpose of a Dirac expression: blockwise `transposeLM` at the transposed
block. CoqQ: `trd` (`dirac.v:239`). -/
noncomputable def transpose (d : Dirac D) : Dirac D :=
  ofFun fun S T => transposeLM (d T S)

end Dirac

/-! ## Notations (scoped to `Qhl`) -/

@[inherit_doc Dirac.comp]
scoped infixr:80 " ∘ᴰ " => Dirac.comp

@[inherit_doc Dirac.tensor]
scoped infixl:100 " ⊗ᴰ " => Dirac.tensor

@[inherit_doc Dirac.dot]
scoped infixl:70 " ·ᴰ " => Dirac.dot

@[inherit_doc Dirac.adj]
scoped postfix:max "†ᴰ" => Dirac.adj

@[inherit_doc Dirac.conj]
scoped postfix:max "ᶜᴰ" => Dirac.conj

@[inherit_doc Dirac.transpose]
scoped postfix:max "ᵀᴰ" => Dirac.transpose

namespace Dirac

/-! ## Blockwise normal forms -/

/-- CoqQ `muldE`-style blockwise value of `∘ᴰ` (`dirac.v:243`). -/
@[simp, dirac_simps]
theorem comp_apply (d₁ d₂ : Dirac D) (S T : Finset L) :
    (d₁ ∘ᴰ d₂) S T = ∑ W : Finset L, d₁ W T ∘ₗ d₂ S W := rfl

/-- CoqQ `adjdE` (`dirac.v:241`). -/
@[simp, dirac_simps]
theorem adj_apply (d : Dirac D) (S T : Finset L) :
    (d†ᴰ) S T = LinearMap.adjoint (d T S) := rfl

/-- CoqQ `conjdE` (`dirac.v:237`). -/
@[simp, dirac_simps]
theorem conj_apply (d : Dirac D) (S T : Finset L) :
    (dᶜᴰ) S T = conjLM (d S T) := rfl

/-- CoqQ `trdE` (`dirac.v:239`). -/
@[simp, dirac_simps]
theorem transpose_apply (d : Dirac D) (S T : Finset L) :
    (dᵀᴰ) S T = transposeLM (d T S) := rfl

/-- Definition unfolding for `⊗ᴰ` (CoqQ `tend`, `dirac.v:249`). -/
theorem tensor_def (d₁ d₂ : Dirac D) :
    d₁ ⊗ᴰ d₂ = ∑ S₁ : Finset L, ∑ T₁ : Finset L, ∑ S₂ : Finset L,
      ∑ T₂ : Finset L, (⌈tenf D (d₁ S₁ T₁) (d₂ S₂ T₂)⌉ᴰ : Dirac D) := rfl

/-- Definition unfolding for `·ᴰ` (CoqQ `dotd`, `dirac.v:246`). -/
theorem dot_def (d₁ d₂ : Dirac D) :
    d₁ ·ᴰ d₂ = ∑ S₁ : Finset L, ∑ T₁ : Finset L, ∑ S₂ : Finset L,
      ∑ T₂ : Finset L, (⌈dotf D (d₁ S₁ T₁) (d₂ S₂ T₂)⌉ᴰ : Dirac D) := rfl

/-! ## Sum-collapse helpers

The four-fold block sums of `⊗ᴰ`/`·ᴰ` applied to `ofBlock`s collapse to the
single on-support term; the hypotheses say that the combinator kills a zero
block (CoqQ discharges the same sums with `big1`/`bigD1`, `dirac.v:398-593`). -/

/-- Collapse `∑ S₂ T₂` over the blocks of `⌈g⌉ᴰ`. -/
theorem sum_block_collapse (g : LinM D S' T')
    (Φ : ∀ S₂ T₂ : Finset L, LinM D S₂ T₂ → Dirac D)
    (hΦ : ∀ S₂ T₂ : Finset L, Φ S₂ T₂ 0 = 0) :
    ∑ S₂ : Finset L, ∑ T₂ : Finset L, Φ S₂ T₂ ((⌈g⌉ᴰ) S₂ T₂) = Φ S' T' g := by
  have hrow : ∀ S₂ ≠ S', ∑ T₂ : Finset L, Φ S₂ T₂ ((⌈g⌉ᴰ) S₂ T₂) = 0 := by
    intro S₂ hS₂
    refine Finset.sum_eq_zero fun T₂ _ => ?_
    rw [ofBlock_apply_of_ne_left _ hS₂, hΦ]
  rw [Fintype.sum_eq_single S' hrow]
  have hcol : ∀ T₂ ≠ T', Φ S' T₂ ((⌈g⌉ᴰ) S' T₂) = 0 := fun T₂ hT₂ => by
    rw [ofBlock_apply_of_ne_right _ hT₂, hΦ]
  rw [Fintype.sum_eq_single T' hcol, ofBlock_apply_self]

/-- Collapse `∑ S₁ T₁ S₂ T₂` over the blocks of `⌈f⌉ᴰ` and `⌈g⌉ᴰ`. -/
theorem sum_block_collapse₂ (f : LinM D S T) (g : LinM D S' T')
    (Φ : ∀ S₁ T₁ S₂ T₂ : Finset L, LinM D S₁ T₁ → LinM D S₂ T₂ → Dirac D)
    (hΦl : ∀ S₁ T₁ S₂ T₂ (g' : LinM D S₂ T₂), Φ S₁ T₁ S₂ T₂ 0 g' = 0)
    (hΦr : ∀ S₁ T₁ S₂ T₂ (f' : LinM D S₁ T₁), Φ S₁ T₁ S₂ T₂ f' 0 = 0) :
    ∑ S₁ : Finset L, ∑ T₁ : Finset L, ∑ S₂ : Finset L, ∑ T₂ : Finset L,
      Φ S₁ T₁ S₂ T₂ ((⌈f⌉ᴰ) S₁ T₁) ((⌈g⌉ᴰ) S₂ T₂) = Φ S T S' T' f g := by
  have hinner : ∀ (S₁ T₁ : Finset L) (x : LinM D S₁ T₁),
      ∑ S₂ : Finset L, ∑ T₂ : Finset L, Φ S₁ T₁ S₂ T₂ x ((⌈g⌉ᴰ) S₂ T₂)
        = Φ S₁ T₁ S' T' x g := fun S₁ T₁ x =>
    sum_block_collapse g (fun S₂ T₂ y => Φ S₁ T₁ S₂ T₂ x y)
      (fun S₂ T₂ => hΦr S₁ T₁ S₂ T₂ x)
  simp only [hinner]
  exact sum_block_collapse f (fun S₁ T₁ x => Φ S₁ T₁ S' T' x g)
    (fun S₁ T₁ => hΦl S₁ T₁ S' T' g)

/-! ## D-5: correctness on `ofBlock` (CoqQ `dirac.v:398-593`) -/

/-- CoqQ `muld_correct` (`dirac.v:508`). -/
@[simp, dirac_simps]
theorem ofBlock_comp (f : LinM D S T) (g : LinM D W S) :
    (⌈f⌉ᴰ ∘ᴰ ⌈g⌉ᴰ : Dirac D) = ⌈f ∘ₗ g⌉ᴰ := by
  ext S₀ T₀
  rw [comp_apply]
  have hU : ∀ U ≠ S, (⌈f⌉ᴰ) U T₀ ∘ₗ (⌈g⌉ᴰ) S₀ U = 0 := fun U hU => by
    rw [ofBlock_apply_of_ne_left _ hU, LinearMap.zero_comp]
  rw [Fintype.sum_eq_single S hU]
  by_cases hS₀ : S₀ = W
  · subst hS₀
    by_cases hT₀ : T₀ = T
    · subst hT₀
      rw [ofBlock_apply_self, ofBlock_apply_self, ofBlock_apply_self]
    · rw [ofBlock_apply_of_ne_right _ hT₀, ofBlock_apply_of_ne_right _ hT₀,
        LinearMap.zero_comp]
  · rw [ofBlock_apply_of_ne_left _ hS₀, ofBlock_apply_of_ne_left _ hS₀,
      LinearMap.comp_zero]

/-- CoqQ `tend_correct` (`dirac.v:527`). -/
@[simp, dirac_simps]
theorem ofBlock_tensor (f : LinM D S T) (g : LinM D S' T') :
    (⌈f⌉ᴰ ⊗ᴰ ⌈g⌉ᴰ : Dirac D) = ⌈tenf D f g⌉ᴰ := by
  rw [tensor_def]
  exact sum_block_collapse₂ f g (fun S₁ T₁ S₂ T₂ x y => ⌈tenf D x y⌉ᴰ)
    (fun _ _ _ _ g' => by rw [tenf_zero_left, ofBlock_zero])
    (fun _ _ _ _ f' => by rw [tenf_zero_right, ofBlock_zero])

/-- CoqQ `dotd_correct` (`dirac.v:537`). -/
@[simp, dirac_simps]
theorem ofBlock_dot (f : LinM D S T) (g : LinM D S' T') :
    (⌈f⌉ᴰ ·ᴰ ⌈g⌉ᴰ : Dirac D) = ⌈dotf D f g⌉ᴰ := by
  rw [dot_def]
  exact sum_block_collapse₂ f g (fun S₁ T₁ S₂ T₂ x y => ⌈dotf D x y⌉ᴰ)
    (fun _ _ _ _ g' => by rw [dotf_zero_left, ofBlock_zero])
    (fun _ _ _ _ f' => by rw [dotf_zero_right, ofBlock_zero])

/-- CoqQ `adjd_correct` (`dirac.v:551-576`). -/
@[simp, dirac_simps]
theorem adj_ofBlock (f : LinM D S T) :
    ((⌈f⌉ᴰ)†ᴰ : Dirac D) = ⌈LinearMap.adjoint f⌉ᴰ := by
  ext S₀ T₀
  rw [adj_apply]
  by_cases h : S₀ = T ∧ T₀ = S
  · obtain ⟨rfl, rfl⟩ := h
    rw [ofBlock_apply_self, ofBlock_apply_self]
  · rcases not_and_or.mp h with h' | h'
    · rw [ofBlock_apply_of_ne_right _ h', ofBlock_apply_of_ne_left _ h', map_zero]
    · rw [ofBlock_apply_of_ne_left _ h', ofBlock_apply_of_ne_right _ h', map_zero]

/-- CoqQ `conjd_correct` (`dirac.v:551-576`). -/
@[simp, dirac_simps]
theorem conj_ofBlock (f : LinM D S T) :
    ((⌈f⌉ᴰ)ᶜᴰ : Dirac D) = ⌈conjLM f⌉ᴰ := by
  ext S₀ T₀
  rw [conj_apply]
  by_cases h : S₀ = S ∧ T₀ = T
  · obtain ⟨rfl, rfl⟩ := h
    rw [ofBlock_apply_self, ofBlock_apply_self]
  · rcases not_and_or.mp h with h' | h'
    · rw [ofBlock_apply_of_ne_left _ h', ofBlock_apply_of_ne_left _ h', conjLM_zero]
    · rw [ofBlock_apply_of_ne_right _ h', ofBlock_apply_of_ne_right _ h',
        conjLM_zero]

/-- CoqQ `trd_correct` (`dirac.v:551-576`). -/
@[simp, dirac_simps]
theorem transpose_ofBlock (f : LinM D S T) :
    ((⌈f⌉ᴰ)ᵀᴰ : Dirac D) = ⌈transposeLM f⌉ᴰ := by
  ext S₀ T₀
  rw [transpose_apply]
  by_cases h : S₀ = T ∧ T₀ = S
  · obtain ⟨rfl, rfl⟩ := h
    rw [ofBlock_apply_self, ofBlock_apply_self]
  · rcases not_and_or.mp h with h' | h'
    · rw [ofBlock_apply_of_ne_right _ h', ofBlock_apply_of_ne_left _ h',
        transposeLM_zero]
    · rw [ofBlock_apply_of_ne_left _ h', ofBlock_apply_of_ne_right _ h',
        transposeLM_zero]

/-! ## D-5: kets, bras and scalars (CoqQ `dirac.v:1845-1884`) -/

/-- Bridge: the operator tensor of two ket maps is the ket map of the vector
tensor, up to the `∅ = ∅ ∪ ∅` cast (CoqQ handles this inside `ketdT`,
`dirac.v:1859`). -/
theorem tenf_toKetM (u : HS D S) (v : HS D T) (h : (∅ : Finset L) = ∅ ∪ ∅) :
    tenf D (toKetM D u) (toKetM D v) = castF D h rfl (toKetM D (tenv D u v)) :=
  linM_ext D fun k => by
    simp only [tenf_deltav, toKetM_apply, deltav_apply,
      eq_iff_true_of_subsingleton, if_true, one_smul, castF_apply, castH_rfl,
      castH_deltav]
    rfl

/-- CoqQ `ketdT` (`dirac.v:1859`): `∣u⟩ᴰ ⊗ᴰ ∣v⟩ᴰ = ∣u ⊗ᵥ v⟩ᴰ`. -/
@[simp, dirac_simps]
theorem ket_tensor_ket (u : HS D S) (v : HS D T) :
    ((∣u⟩ᴰ : Dirac D) ⊗ᴰ ∣v⟩ᴰ) = ∣tenv D u v⟩ᴰ := by
  rw [ket, ket, ket, ofBlock_tensor, tenf_toKetM u v (by simp), ofBlock_castF]

/-- CoqQ `innerM` (`dirac.v:1845`): `⟨u∣ᴰ ∘ᴰ ∣v⟩ᴰ = ⟪u, v⟫ᴰ` (inner product,
conjugate-linear in `u`). -/
@[simp, dirac_simps]
theorem bra_comp_ket (u v : HS D S) :
    ((⟨u∣ᴰ : Dirac D) ∘ᴰ ∣v⟩ᴰ) = num D ⟪u, v⟫ := by
  rw [bra, ket, ofBlock_comp, comp_dot, num]

/-- CoqQ `outerM` (`dirac.v:1849`): `∣v⟩ᴰ ∘ᴰ ⟨u∣ᴰ = ⌈outerLM v u⌉ᴰ`. -/
@[simp, dirac_simps]
theorem ket_comp_bra (u v : HS D S) :
    ((∣v⟩ᴰ : Dirac D) ∘ᴰ ⟨u∣ᴰ) = ⌈outerLM v u⌉ᴰ := by
  rw [ket, bra, ofBlock_comp, comp_out]

/-- CoqQ `lind_ketG` (`dirac.v:1884`): operators act on kets through `·ᴰ`. -/
@[simp, dirac_simps]
theorem ofBlock_dot_ket (f : LinM D S T) (v : HS D S) :
    ((⌈f⌉ᴰ : Dirac D) ·ᴰ ∣v⟩ᴰ) = ∣f v⟩ᴰ := by
  rw [ket, ofBlock_dot, dotf_comp D (by simp) (by simp) f (toKetM D v),
    comp_toKetM, ofBlock_castF, ket]

/-! ## D-6 (bilinearity part): the three products are bilinear
(CoqQ `dirac.v:681-871`); `†ᴰ`/`ᶜᴰ` are antilinear and `ᵀᴰ` is linear
(the instances accompanying CoqQ `adjd/conjd/trd`, `dirac.v:237-241`).
Naming: `_left`/`_right` is the operand of the product that varies. -/

/-- CoqQ `muldDl` (`dirac.v:681-871`). -/
theorem comp_add_left (d₁ d₂ e : Dirac D) :
    (d₁ + d₂) ∘ᴰ e = d₁ ∘ᴰ e + d₂ ∘ᴰ e := by
  ext S₀ T₀
  simp only [comp_apply, add_apply, LinearMap.add_comp, Finset.sum_add_distrib]

/-- CoqQ `muldDr` (`dirac.v:681-871`). -/
theorem comp_add_right (d e₁ e₂ : Dirac D) :
    d ∘ᴰ (e₁ + e₂) = d ∘ᴰ e₁ + d ∘ᴰ e₂ := by
  ext S₀ T₀
  simp only [comp_apply, add_apply, LinearMap.comp_add, Finset.sum_add_distrib]

/-- CoqQ `muldZl` (`dirac.v:681-871`). -/
theorem comp_smul_left (c : ℂ) (d e : Dirac D) :
    (c • d) ∘ᴰ e = c • (d ∘ᴰ e) := by
  ext S₀ T₀
  simp only [comp_apply, smul_apply, LinearMap.smul_comp, Finset.smul_sum]

/-- CoqQ `muldZr` (`dirac.v:681-871`). -/
theorem comp_smul_right (c : ℂ) (d e : Dirac D) :
    d ∘ᴰ (c • e) = c • (d ∘ᴰ e) := by
  ext S₀ T₀
  simp only [comp_apply, smul_apply, LinearMap.comp_smul, Finset.smul_sum]

/-- CoqQ `mul0d` (`dirac.v:681-871`). -/
@[simp, dirac_simps]
theorem comp_zero_left (e : Dirac D) : (0 : Dirac D) ∘ᴰ e = 0 := by
  ext S₀ T₀
  simp only [comp_apply, zero_apply, LinearMap.zero_comp, Finset.sum_const_zero]

/-- CoqQ `muld0` (`dirac.v:681-871`). -/
@[simp, dirac_simps]
theorem comp_zero_right (d : Dirac D) : d ∘ᴰ (0 : Dirac D) = 0 := by
  ext S₀ T₀
  simp only [comp_apply, zero_apply, LinearMap.comp_zero, Finset.sum_const_zero]

/-- CoqQ `tendDl` (`dirac.v:681-871`). -/
theorem tensor_add_left (d₁ d₂ e : Dirac D) :
    (d₁ + d₂) ⊗ᴰ e = d₁ ⊗ᴰ e + d₂ ⊗ᴰ e := by
  simp only [tensor_def, add_apply, tenf_add_left, ofBlock_add,
    Finset.sum_add_distrib]

/-- CoqQ `tendDr` (`dirac.v:681-871`). -/
theorem tensor_add_right (d e₁ e₂ : Dirac D) :
    d ⊗ᴰ (e₁ + e₂) = d ⊗ᴰ e₁ + d ⊗ᴰ e₂ := by
  simp only [tensor_def, add_apply, tenf_add_right, ofBlock_add,
    Finset.sum_add_distrib]

/-- CoqQ `tendZl` (`dirac.v:681-871`). -/
theorem tensor_smul_left (c : ℂ) (d e : Dirac D) :
    (c • d) ⊗ᴰ e = c • (d ⊗ᴰ e) := by
  simp only [tensor_def, smul_apply, tenf_smul_left, ofBlock_smul,
    Finset.smul_sum]

/-- CoqQ `tendZr` (`dirac.v:681-871`). -/
theorem tensor_smul_right (c : ℂ) (d e : Dirac D) :
    d ⊗ᴰ (c • e) = c • (d ⊗ᴰ e) := by
  simp only [tensor_def, smul_apply, tenf_smul_right, ofBlock_smul,
    Finset.smul_sum]

/-- CoqQ `ten0d` (`dirac.v:681-871`). -/
@[simp, dirac_simps]
theorem tensor_zero_left (e : Dirac D) : (0 : Dirac D) ⊗ᴰ e = 0 := by
  simp only [tensor_def, zero_apply, tenf_zero_left, ofBlock_zero,
    Finset.sum_const_zero]

/-- CoqQ `tend0` (`dirac.v:681-871`). -/
@[simp, dirac_simps]
theorem tensor_zero_right (d : Dirac D) : d ⊗ᴰ (0 : Dirac D) = 0 := by
  simp only [tensor_def, zero_apply, tenf_zero_right, ofBlock_zero,
    Finset.sum_const_zero]

/-- CoqQ `dotdDl` (`dirac.v:681-871`). -/
theorem dot_add_left (d₁ d₂ e : Dirac D) :
    (d₁ + d₂) ·ᴰ e = d₁ ·ᴰ e + d₂ ·ᴰ e := by
  simp only [dot_def, add_apply, dotf_add_left, ofBlock_add,
    Finset.sum_add_distrib]

/-- CoqQ `dotdDr` (`dirac.v:681-871`). -/
theorem dot_add_right (d e₁ e₂ : Dirac D) :
    d ·ᴰ (e₁ + e₂) = d ·ᴰ e₁ + d ·ᴰ e₂ := by
  simp only [dot_def, add_apply, dotf_add_right, ofBlock_add,
    Finset.sum_add_distrib]

/-- CoqQ `dotdZl` (`dirac.v:681-871`). -/
theorem dot_smul_left (c : ℂ) (d e : Dirac D) :
    (c • d) ·ᴰ e = c • (d ·ᴰ e) := by
  simp only [dot_def, smul_apply, dotf_smul_left, ofBlock_smul, Finset.smul_sum]

/-- CoqQ `dotdZr` (`dirac.v:681-871`). -/
theorem dot_smul_right (c : ℂ) (d e : Dirac D) :
    d ·ᴰ (c • e) = c • (d ·ᴰ e) := by
  simp only [dot_def, smul_apply, dotf_smul_right, ofBlock_smul, Finset.smul_sum]

/-- CoqQ `dot0d` (`dirac.v:681-871`). -/
@[simp, dirac_simps]
theorem dot_zero_left (e : Dirac D) : (0 : Dirac D) ·ᴰ e = 0 := by
  simp only [dot_def, zero_apply, dotf_zero_left, ofBlock_zero,
    Finset.sum_const_zero]

/-- CoqQ `dotd0` (`dirac.v:681-871`). -/
@[simp, dirac_simps]
theorem dot_zero_right (d : Dirac D) : d ·ᴰ (0 : Dirac D) = 0 := by
  simp only [dot_def, zero_apply, dotf_zero_right, ofBlock_zero,
    Finset.sum_const_zero]

/-- `†ᴰ` is additive (CoqQ `adjd` antilinear instance, `dirac.v:241`). -/
theorem adj_add (d e : Dirac D) : (d + e)†ᴰ = d†ᴰ + e†ᴰ := by
  ext S₀ T₀
  simp only [adj_apply, add_apply, map_add]

/-- `†ᴰ` is conjugate-homogeneous (CoqQ `adjd` antilinear instance,
`dirac.v:241`). -/
theorem adj_smul (c : ℂ) (d : Dirac D) : (c • d)†ᴰ = star c • d†ᴰ := by
  ext S₀ T₀
  simp only [adj_apply, smul_apply, map_smulₛₗ, starRingEnd_apply]

/-- `†ᴰ` preserves zero (CoqQ `adjd`, `dirac.v:241`). -/
@[simp, dirac_simps]
theorem adj_zero : ((0 : Dirac D))†ᴰ = 0 := by
  ext S₀ T₀
  simp only [adj_apply, zero_apply, map_zero]

/-- `ᶜᴰ` is additive (CoqQ `conjd` antilinear instance, `dirac.v:237`). -/
theorem conj_add (d e : Dirac D) : (d + e)ᶜᴰ = dᶜᴰ + eᶜᴰ := by
  ext S₀ T₀
  simp only [conj_apply, add_apply, conjLM_add]

/-- `ᶜᴰ` is conjugate-homogeneous (CoqQ `conjd` antilinear instance,
`dirac.v:237`). -/
theorem conj_smul (c : ℂ) (d : Dirac D) : (c • d)ᶜᴰ = star c • dᶜᴰ := by
  ext S₀ T₀
  simp only [conj_apply, smul_apply, conjLM_smul]

/-- `ᶜᴰ` preserves zero (CoqQ `conjd`, `dirac.v:237`). -/
@[simp, dirac_simps]
theorem conj_zero : ((0 : Dirac D))ᶜᴰ = 0 := by
  ext S₀ T₀
  simp only [conj_apply, zero_apply, conjLM_zero]

/-- `ᵀᴰ` is additive (CoqQ `trd` linear instance, `dirac.v:239`). -/
theorem transpose_add (d e : Dirac D) : (d + e)ᵀᴰ = dᵀᴰ + eᵀᴰ := by
  ext S₀ T₀
  simp only [transpose_apply, add_apply, transposeLM_add]

/-- `ᵀᴰ` is ℂ-homogeneous — genuinely linear, unlike `†ᴰ`/`ᶜᴰ` (CoqQ `trd`
linear instance, `dirac.v:239`; layer 1 `transposeLM_smul`). -/
theorem transpose_smul (c : ℂ) (d : Dirac D) : (c • d)ᵀᴰ = c • dᵀᴰ := by
  ext S₀ T₀
  simp only [transpose_apply, smul_apply, transposeLM_smul]

/-- `ᵀᴰ` preserves zero (CoqQ `trd`, `dirac.v:239`). -/
@[simp, dirac_simps]
theorem transpose_zero : ((0 : Dirac D))ᵀᴰ = 0 := by
  ext S₀ T₀
  simp only [transpose_apply, zero_apply, transposeLM_zero]

end Dirac

end Qhl
