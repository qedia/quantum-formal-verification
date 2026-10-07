import Qhl.Dirac.WF
import Qhl.Tactic.FinsetDec

/-!
# The labelled laws (D-L1..D-L9)

Mirror of `CoqQ/src/dirac/dirac.v:1693-2130` (spec 03 §4): the equations
between `·ᴰ`, `⊗ᴰ` and `∘ᴰ` that hold for *well-formed* Dirac expressions
under `Finset` disjointness side conditions. All side conditions are
discharged by `finset_dec` (spec 02 §7).

* D-L1 `dot_eq_tensor` (CoqQ `dotd_ten:1746`), D-L2 `dot_eq_comp`
  (`dotd_mul:1777`), D-L5 `dot_comm` (`dotdC:1753`)
* D-L3 `tensor_comp_interchange` (`tend_mul:1793`)
* D-L4 `dot_assoc_cond` (`dotdA_cond:1714`), `dot_assoc_of_sq` (`dotdA:1728`)
* identity laws: `one_comp_of_wf`/`comp_one_of_wf` (`mulId`/`muldI:1786`),
  `dot_multen` (`dotd_multen:1832`), D-L6 `one_dot`/`dot_one`
  (`dotIdT:1801`/`dotdIT:1807`), `one_dot_sdiff`/`dot_one_sdiff`
  (`dotId`/`dotdI:1813-1816`), absorption `one_dot_of_subset`/
  `dot_one_of_subset` (`dotIdid:1819`/`dotdIid:1822`), `one_empty`, D-L7
  `one_tensor_one`/`one_dot_one` (`tendII:1836`/`dotdII:1839`)
* D-L8 push-through `dot_tensor_ll/lr/rl/rr` (`dotdTll…:1926-1954`) — derived
  at the Dirac level from `dot_multen` + D-L3, no new layer-1 lemma
* D-L9 `prod_bra_comp_prod_ket` (`innerMBT:2103`)

Proof scheme (spec 03 §5): rewrite the operands into block form with
`WFAt.eq`, apply the D-5 correctness laws, conclude with the layer-1 fact and
let `ofBlock_castF` absorb the cast.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

variable {L : Type*} [Fintype L] [DecidableEq L] {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
  {S T W W' S' T' S₁ T₁ S₂ T₂ S₃ T₃ : Finset L}

namespace Dirac

variable {d d₁ d₂ d₃ d₄ : Dirac D}

/-! ## D-L1, D-L2, D-L5 (CoqQ `dotd_ten:1746`, `dotd_mul:1777`,
`dotdC:1753`) -/

/-- **D-L1**: on disjoint supports the dot is the tensor.
CoqQ `dotd_ten` (`dirac.v:1746`). -/
theorem dot_eq_tensor (h₁ : WFAt S T d₁) (h₂ : WFAt S' T' d₂)
    (hd : Disjoint S T') : d₁ ·ᴰ d₂ = d₁ ⊗ᴰ d₂ := by
  rw [← h₁.eq, ← h₂.eq, ofBlock_dot, ofBlock_tensor,
    dotf_ten D hd (by finset_dec) (by finset_dec) (d₁ S T) (d₂ S' T'),
    ofBlock_castF]

/-- **D-L2**: on composable supports the dot is the composition.
CoqQ `dotd_mul` (`dirac.v:1777`). -/
theorem dot_eq_comp (h₁ : WFAt S T d₁) (h₂ : WFAt W S d₂) :
    d₁ ·ᴰ d₂ = d₁ ∘ᴰ d₂ := by
  rw [← h₁.eq, ← h₂.eq, ofBlock_dot, ofBlock_comp,
    dotf_comp D (by finset_dec) (by finset_dec) (d₁ S T) (d₂ W S),
    ofBlock_castF]

/-- **D-L5**: the dot commutes when the supports do not interact on either
side. CoqQ `dotdC` (`dirac.v:1753`). -/
theorem dot_comm (h₁ : WFAt S T d₁) (h₂ : WFAt S' T' d₂)
    (hd₁ : Disjoint S T') (hd₂ : Disjoint T S') : d₁ ·ᴰ d₂ = d₂ ·ᴰ d₁ := by
  rw [dot_eq_tensor h₁ h₂ hd₁, dot_eq_tensor h₂ h₁ hd₂.symm, tensor_comm]

/-! ## D-L3: the interchange law (CoqQ `tend_mul:1793`) -/

/-- **D-L3**: composition and tensor interchange, given disjoint middle
supports. CoqQ `tend_mul` (`dirac.v:1793`). -/
theorem tensor_comp_interchange (h₁ : WFAt S T d₁) (h₂ : WFAt W S d₂)
    (h₃ : WFAt S' T' d₃) (h₄ : WFAt W' S' d₄) (hd : Disjoint S S') :
    (d₁ ⊗ᴰ d₃) ∘ᴰ (d₂ ⊗ᴰ d₄) = (d₁ ∘ᴰ d₂) ⊗ᴰ (d₃ ∘ᴰ d₄) := by
  rw [← h₁.eq, ← h₂.eq, ← h₃.eq, ← h₄.eq]
  simp only [ofBlock_tensor, ofBlock_comp]
  rw [← tenf_comp D hd (d₁ S T) (d₃ S' T') (d₂ W S) (d₄ W' S')]

/-! ## D-L4: conditional associativity (CoqQ `dotdA_cond:1714`,
`dotdA:1728`) -/

/-- **D-L4**, general form: the dot is associative under CoqQ's two
disjointness side conditions. CoqQ `dotdA_cond` (`dirac.v:1714`). -/
theorem dot_assoc_cond (h₁ : WFAt S₁ T₁ d₁) (h₂ : WFAt S₂ T₂ d₂)
    (h₃ : WFAt S₃ T₃ d₃) (P1 : Disjoint S₂ (S₁ \ T₂))
    (P2 : Disjoint T₂ (T₃ \ S₂)) :
    d₁ ·ᴰ (d₂ ·ᴰ d₃) = (d₁ ·ᴰ d₂) ·ᴰ d₃ := by
  rw [← h₁.eq, ← h₂.eq, ← h₃.eq]
  simp only [ofBlock_dot]
  rw [← dotf_assoc D P1 P2 (by finset_dec) (by finset_dec)
      (d₁ S₁ T₁) (d₂ S₂ T₂) (d₃ S₃ T₃),
    ofBlock_castF]

/-- **D-L4**, square-middle form: the dot is associative whenever the middle
factor is a square operator. CoqQ `dotdA` (`dirac.v:1728`). -/
theorem dot_assoc_of_sq (h₁ : WFAt S₁ T₁ d₁) (h₂ : IsSqOn S₂ d₂)
    (h₃ : WFAt S₃ T₃ d₃) : d₁ ·ᴰ (d₂ ·ᴰ d₃) = (d₁ ·ᴰ d₂) ·ᴰ d₃ :=
  dot_assoc_cond h₁ h₂ h₃ (by finset_dec) (by finset_dec)

/-! ## Identity laws (CoqQ `mulId`/`muldI:1786`, `dotd_multen:1832`,
`dotIdT:1801`-`dotdIid:1822`, `tendII:1836`, `dotdII:1839`) -/

/-- `𝟙ᴰ` is a left unit for `∘ᴰ` on wf expressions. CoqQ `mulId`
(`dirac.v:1786`). -/
theorem one_comp_of_wf (h : WFAt S T d) : (𝟙ᴰ T : Dirac D) ∘ᴰ d = d := by
  rw [← h.eq, one, ofBlock_comp, one_comp]

/-- `𝟙ᴰ` is a right unit for `∘ᴰ` on wf expressions. CoqQ `muldI`
(`dirac.v:1786`). -/
theorem comp_one_of_wf (h : WFAt S T d) : d ∘ᴰ (𝟙ᴰ S : Dirac D) = d := by
  rw [← h.eq, one, ofBlock_comp, comp_one]

/-- **D-L7**, tensor part: identities tensor to the identity of the union.
CoqQ `tendII` (`dirac.v:1836`). -/
theorem one_tensor_one (S T : Finset L) :
    (𝟙ᴰ S : Dirac D) ⊗ᴰ 𝟙ᴰ T = 𝟙ᴰ (S ∪ T) := by
  rw [one, one, one, ofBlock_tensor, tenf_one_one]

/-- The dot as an identity-padded composition (the Dirac-level image of the
*definition* of `dotf`). CoqQ `dotd_multen` (`dirac.v:1832`). -/
theorem dot_multen (h₁ : WFAt S T d₁) (h₂ : WFAt S' T' d₂) :
    d₁ ·ᴰ d₂ = (d₁ ⊗ᴰ 𝟙ᴰ (T' \ S)) ∘ᴰ (d₂ ⊗ᴰ 𝟙ᴰ (S \ T')) := by
  rw [← h₁.eq, ← h₂.eq, one, one, ofBlock_tensor, ofBlock_tensor, ofBlock_dot,
    dotf, ← ofBlock_comp, ofBlock_castF]

/-- **D-L6**: dotting `𝟙ᴰ W` onto `d` keeps only the part of `W` not covered
by `d`'s output. CoqQ `dotIdT` (`dirac.v:1801`). -/
theorem one_dot (h : WFAt S T d) :
    (𝟙ᴰ W : Dirac D) ·ᴰ d = 𝟙ᴰ (W \ T) ⊗ᴰ d := by
  rw [dot_multen wf_one h, one_tensor_one,
    one_comp_of_wf ((h.tensor wf_one).cast rfl
      ((by finset_dec : T ∪ W \ T = W ∪ T \ W))),
    tensor_comm]

/-- **D-L6**, mirror: dotting `d` onto `𝟙ᴰ W` keeps only the part of `W` not
covered by `d`'s input. CoqQ `dotdIT` (`dirac.v:1807`). -/
theorem dot_one (h : WFAt S T d) :
    d ·ᴰ (𝟙ᴰ W : Dirac D) = 𝟙ᴰ (W \ S) ⊗ᴰ d := by
  have h' := congrArg adj (one_dot h.adj (W := W))
  rw [adj_dot, adj_tensor, adj_one, adj_one, adj_adj] at h'
  exact h'

/-- The identity operand of a dot can be trimmed. CoqQ `dotId`
(`dirac.v:1813`). -/
theorem one_dot_sdiff (h : WFAt S T d) :
    (𝟙ᴰ W : Dirac D) ·ᴰ d = 𝟙ᴰ (W \ T) ·ᴰ d := by
  rw [one_dot h, dot_eq_tensor wf_one h (by finset_dec)]

/-- The identity operand of a dot can be trimmed, mirror. CoqQ `dotdI`
(`dirac.v:1816`). -/
theorem dot_one_sdiff (h : WFAt S T d) :
    d ·ᴰ (𝟙ᴰ W : Dirac D) = d ·ᴰ 𝟙ᴰ (W \ S) := by
  rw [dot_one h, dot_eq_tensor h wf_one (by finset_dec), tensor_comm]

/-- The empty-register identity is the ring unit (the scalar `1ᴰ`).
CoqQ `lindI1`-area (`dirac.v:1706`). -/
@[simp, dirac_simps]
theorem one_empty : (𝟙ᴰ (∅ : Finset L) : Dirac D) = 1 := by
  rw [one, one_def, num, toScalarM_one]

/-- **D-L6**, absorption: an identity covered by `d`'s output is absorbed.
CoqQ `dotIdid` (`dirac.v:1819`). -/
theorem one_dot_of_subset (h : WFAt S T d) (hW : W ⊆ T) :
    (𝟙ᴰ W : Dirac D) ·ᴰ d = d := by
  rw [one_dot h, (by finset_dec : W \ T = ∅), one_empty, one_def,
    num_one_tensor]

/-- **D-L6**, absorption mirror: an identity covered by `d`'s input is
absorbed. CoqQ `dotdIid` (`dirac.v:1822`). -/
theorem dot_one_of_subset (h : WFAt S T d) (hW : W ⊆ S) :
    d ·ᴰ (𝟙ᴰ W : Dirac D) = d := by
  rw [dot_one h, (by finset_dec : W \ S = ∅), one_empty, one_def,
    num_one_tensor]

/-- **D-L7**, dot part: identities dot to the identity of the union.
CoqQ `dotdII` (`dirac.v:1839`). -/
theorem one_dot_one (S T : Finset L) :
    (𝟙ᴰ S : Dirac D) ·ᴰ 𝟙ᴰ T = 𝟙ᴰ (S ∪ T) := by
  rw [one_dot wf_one, one_tensor_one, (by finset_dec : S \ T ∪ T = S ∪ T)]

/-! ## D-L8: pushing `·ᴰ` through a `⊗ᴰ` factor (CoqQ `dotdTll`-`dotdTrr`,
`dirac.v:1926-1954`)

All four variants are derived at the Dirac level from `dot_multen` + D-L3 +
the `⊗ᴰ`-ring laws — no `dotfTl`/`dotfTr` layer-1 port needed. -/

/-- **D-L8**: push a left dot operand into the left tensor factor.
CoqQ `dotdTll` (`dirac.v:1926`). -/
theorem dot_tensor_ll (h₁ : WFAt S₁ T₁ d₁) (h₂ : WFAt S₂ T₂ d₂)
    (h₃ : WFAt S₃ T₃ d₃) (P1 : Disjoint S₁ T₃) (P2 : Disjoint T₂ T₃) :
    d₁ ·ᴰ (d₂ ⊗ᴰ d₃) = (d₁ ·ᴰ d₂) ⊗ᴰ d₃ := by
  have e₁ : S₁ \ (T₂ ∪ T₃) = S₁ \ T₂ := by finset_dec
  have e₂ : (T₂ ∪ T₃) \ S₁ = T₂ \ S₁ ∪ T₃ := by finset_dec
  have sh : d₂ ⊗ᴰ d₃ ⊗ᴰ (𝟙ᴰ (S₁ \ T₂) : Dirac D)
      = (d₂ ⊗ᴰ 𝟙ᴰ (S₁ \ T₂)) ⊗ᴰ d₃ := by
    simp only [← mul_def]; ring
  rw [dot_multen h₁ (h₂.tensor h₃), dot_multen h₁ h₂, e₁, e₂,
    ← one_tensor_one, ← tensor_assoc, sh,
    tensor_comp_interchange (h₁.tensor wf_one)
      ((h₂.tensor wf_one).cast rfl (by finset_dec)) wf_one h₃ (by finset_dec),
    one_comp_of_wf h₃]

/-- **D-L8**: push a left dot operand into the right tensor factor.
CoqQ `dotdTlr` (`dirac.v:1934`). -/
theorem dot_tensor_lr (h₁ : WFAt S₁ T₁ d₁) (h₂ : WFAt S₂ T₂ d₂)
    (h₃ : WFAt S₃ T₃ d₃) (P1 : Disjoint S₁ T₂) (P2 : Disjoint T₃ T₂) :
    d₁ ·ᴰ (d₂ ⊗ᴰ d₃) = d₂ ⊗ᴰ (d₁ ·ᴰ d₃) := by
  rw [tensor_comm d₂ d₃, dot_tensor_ll h₁ h₃ h₂ P1 P2, tensor_comm]

/-- **D-L8**: push a right dot operand into the left tensor factor.
CoqQ `dotdTrl` (`dirac.v:1940`). -/
theorem dot_tensor_rl (h₁ : WFAt S₁ T₁ d₁) (h₂ : WFAt S₂ T₂ d₂)
    (h₃ : WFAt S₃ T₃ d₃) (P1 : Disjoint T₁ S₃) (P2 : Disjoint S₂ S₃) :
    (d₂ ⊗ᴰ d₃) ·ᴰ d₁ = (d₂ ·ᴰ d₁) ⊗ᴰ d₃ := by
  have e₁ : T₁ \ (S₂ ∪ S₃) = T₁ \ S₂ := by finset_dec
  have e₂ : (S₂ ∪ S₃) \ T₁ = S₂ \ T₁ ∪ S₃ := by finset_dec
  have sh : d₂ ⊗ᴰ d₃ ⊗ᴰ (𝟙ᴰ (T₁ \ S₂) : Dirac D)
      = (d₂ ⊗ᴰ 𝟙ᴰ (T₁ \ S₂)) ⊗ᴰ d₃ := by
    simp only [← mul_def]; ring
  rw [dot_multen (h₂.tensor h₃) h₁, dot_multen h₂ h₁, e₁, e₂,
    ← one_tensor_one, ← tensor_assoc, sh,
    tensor_comp_interchange (h₂.tensor wf_one)
      ((h₁.tensor wf_one).cast rfl (by finset_dec)) h₃ wf_one (by finset_dec),
    comp_one_of_wf h₃]

/-- **D-L8**: push a right dot operand into the right tensor factor.
CoqQ `dotdTrr` (`dirac.v:1948`). -/
theorem dot_tensor_rr (h₁ : WFAt S₁ T₁ d₁) (h₂ : WFAt S₂ T₂ d₂)
    (h₃ : WFAt S₃ T₃ d₃) (P1 : Disjoint T₁ S₂) (P2 : Disjoint S₃ S₂) :
    (d₂ ⊗ᴰ d₃) ·ᴰ d₁ = d₂ ⊗ᴰ (d₃ ·ᴰ d₁) := by
  rw [tensor_comm d₂ d₃, dot_tensor_rl h₁ h₃ h₂ P1 P2, tensor_comm]

/-! ## D-L9: the big inner product (CoqQ `innerMBT:2103`) -/

/-- **D-L9**: a big tensor of bras composed with a big tensor of kets on a
pairwise-disjoint family of registers is the big tensor of the inner
products. CoqQ `innerMBT` (`dirac.v:2103`). -/
theorem prod_bra_comp_prod_ket {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → Finset L} (hd : Pairwise (Function.onFun Disjoint f))
    (u v : ∀ j, HS D (f j)) :
    (∏ j, (⟨u j∣ᴰ : Dirac D)) ∘ᴰ (∏ j, (∣v j⟩ᴰ : Dirac D))
      = ∏ j, num D ⟪u j, v j⟫ := by
  rw [prod_bra, prod_ket, bra_comp_ket, tenvFamily_inner D f hd, num_prod]

end Dirac

end Qhl
