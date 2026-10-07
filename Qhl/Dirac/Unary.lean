import Qhl.Dirac.Products

/-!
# The unary operators `†ᴰ`/`ᶜᴰ`/`ᵀᴰ`: involutions, lattice, anti-multiplicativity

Mirror of `CoqQ/src/dirac/dirac.v:904-1037` and `916-1010` (spec 03 §3,
subgoal D-7).

* Layer-1 bridges: `conjLM`/`transposeLM` on `toKetM`/`toBraM`/`toScalarM`
  and the identity (they conjugate the vector via `conjV`)
* Involutions: `adj_adj`, `conj_conj`, `transpose_transpose`
  (CoqQ `adjdK:906`, `conjdK:904`, `trdK:908`)
* The 6-identity lattice `<outer>_<inner>`: `conj_adj`/`adj_conj` (`= ᵀᴰ`),
  `transpose_conj`/`conj_transpose` (`= †ᴰ`), `adj_transpose`/`transpose_adj`
  (`= ᶜᴰ`) — CoqQ `dirac.v:910-937`; corollaries `transpose_eq_conj_adj`,
  `adj_conj_comm`
* Additivity over sums: `adj_sum`, `conj_sum`, `transpose_sum`
  (CoqQ `dirac.v:942-960`-area)
* (Anti-)multiplicativity: `adj_comp`/`adj_tensor`/`adj_dot` (CoqQ
  `adjdM:964`, `adjdT:969`, `adjdG:975`), `conj_comp`/`conj_tensor`/`conj_dot`
  (multiplicative, *no* swap; CoqQ `conjdM/conjdT/conjdG`),
  `transpose_comp`/`transpose_tensor`/`transpose_dot` (swaps `∘ᴰ`/`·ᴰ` like
  `†ᴰ`; CoqQ `trdM/trdT/trdG`, all in `dirac.v:916-1010`) — deliberately *not*
  `simp` (they would fight `ring`-normal forms)
* Constructors under the unaries: `adj_ket/bra/num/one`,
  `conj_ket/bra/num/one`, `transpose_ket/bra/num/one`
  (CoqQ `dirac.v:916-1010`)
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L] {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] {S T W S' T' : Finset L}

/-! ## Layer-1 bridges: `conjLM`/`transposeLM` on kets, bras, scalars, `1`

`conjV` fixes `deltav` (`conjV_deltav`), so conjugation/transposition of the
block maps of `Qhl/HSpace/KetBra.lean` conjugates the underlying vector.
(CoqQ works with `v2f/v2df` conversions inline, `dirac.v:916-1010`.) -/

/-- C on a ket map conjugates the ket. -/
@[simp]
theorem conjLM_toKetM (v : HS D S) : conjLM (toKetM D v) = toKetM D (conjV v) := by
  rw [toKetM_def, toKetM_def, conjLM_outerLM, conjV_deltav]

/-- C on a bra map conjugates the bra. -/
@[simp]
theorem conjLM_toBraM (v : HS D S) : conjLM (toBraM D v) = toBraM D (conjV v) := by
  rw [toBraM_def, toBraM_def, conjLM_outerLM, conjV_deltav]

/-- T sends a ket map to the conjugated bra map. -/
@[simp]
theorem transposeLM_toKetM (v : HS D S) :
    transposeLM (toKetM D v) = toBraM D (conjV v) := by
  rw [toKetM_def, toBraM_def, transposeLM_outerLM, conjV_deltav]

/-- T sends a bra map to the conjugated ket map. -/
@[simp]
theorem transposeLM_toBraM (v : HS D S) :
    transposeLM (toBraM D v) = toKetM D (conjV v) := by
  rw [toBraM_def, toKetM_def, transposeLM_outerLM, conjV_deltav]

/-- C on a scalar map is the conjugate scalar map. -/
@[simp]
theorem conjLM_toScalarM (c : ℂ) :
    conjLM (toScalarM D c) = toScalarM D (star c) := by
  rw [toScalarM_def, toScalarM_def, conjLM_smul, conjLM_one]

/-- T fixes scalar maps (`ᵀ = ᶜ ∘ †` and both stars cancel). -/
@[simp]
theorem transposeLM_toScalarM (c : ℂ) :
    transposeLM (toScalarM D c) = toScalarM D c := by
  rw [← adjoint_conjLM, conjLM_toScalarM, adjoint_toScalarM, star_star]

/-- T fixes the identity operator. -/
@[simp]
theorem transposeLM_one : transposeLM (1 : EndM D W) = 1 := by
  rw [← adjoint_conjLM, conjLM_one, LinearMap.adjoint_one]

namespace Dirac

/-! ## D-7: involutions (CoqQ `conjdK:904`, `adjdK:906`, `trdK:908`) -/

/-- `†ᴰ` is involutive. CoqQ `adjdK` (`dirac.v:906`). -/
@[simp, dirac_simps]
theorem adj_adj (d : Dirac D) : (d†ᴰ)†ᴰ = d :=
  ext fun _ _ => by simp only [adj_apply, LinearMap.adjoint_adjoint]

/-- `ᶜᴰ` is involutive. CoqQ `conjdK` (`dirac.v:904`). -/
@[simp, dirac_simps]
theorem conj_conj (d : Dirac D) : (dᶜᴰ)ᶜᴰ = d :=
  ext fun _ _ => by simp only [conj_apply, conjLM_conjLM]

/-- `ᵀᴰ` is involutive. CoqQ `trdK` (`dirac.v:908`). -/
@[simp, dirac_simps]
theorem transpose_transpose (d : Dirac D) : (dᵀᴰ)ᵀᴰ = d :=
  ext fun _ _ => by simp only [transpose_apply, transposeLM_transposeLM]

/-! ## D-7: the 6-identity lattice (CoqQ `dirac.v:910-937`) -/

/-- C ∘ A = T. CoqQ `trdAC`-area (`dirac.v:910-937`). -/
@[simp, dirac_simps]
theorem conj_adj (d : Dirac D) : (d†ᴰ)ᶜᴰ = dᵀᴰ :=
  ext fun _ _ => by simp only [conj_apply, adj_apply, transpose_apply,
    conjLM_adjoint]

/-- A ∘ C = T. CoqQ `trdCA`-area (`dirac.v:910-937`). -/
@[simp, dirac_simps]
theorem adj_conj (d : Dirac D) : (dᶜᴰ)†ᴰ = dᵀᴰ :=
  ext fun _ _ => by simp only [adj_apply, conj_apply, transpose_apply,
    adjoint_conjLM]

/-- T ∘ C = A. CoqQ `adjdTC`-area (`dirac.v:910-937`). -/
@[simp, dirac_simps]
theorem transpose_conj (d : Dirac D) : (dᶜᴰ)ᵀᴰ = d†ᴰ :=
  ext fun _ _ => by simp only [transpose_apply, conj_apply, adj_apply,
    transposeLM_conjLM]

/-- C ∘ T = A. CoqQ `adjdCT`-area (`dirac.v:910-937`). -/
@[simp, dirac_simps]
theorem conj_transpose (d : Dirac D) : (dᵀᴰ)ᶜᴰ = d†ᴰ :=
  ext fun _ _ => by simp only [conj_apply, transpose_apply, adj_apply,
    conjLM_transposeLM]

/-- A ∘ T = C. CoqQ `conjdAT`-area (`dirac.v:910-937`). -/
@[simp, dirac_simps]
theorem adj_transpose (d : Dirac D) : (dᵀᴰ)†ᴰ = dᶜᴰ :=
  ext fun _ _ => by simp only [adj_apply, transpose_apply, conj_apply,
    adjoint_transposeLM]

/-- T ∘ A = C. CoqQ `conjdTA`-area (`dirac.v:910-937`). -/
@[simp, dirac_simps]
theorem transpose_adj (d : Dirac D) : (d†ᴰ)ᵀᴰ = dᶜᴰ :=
  ext fun _ _ => by simp only [transpose_apply, adj_apply, conj_apply,
    transposeLM_adjoint]

/-- `dᵀ = (d†)ᶜ`, the defining relation of the lattice (spec 03, D-7). -/
theorem transpose_eq_conj_adj (d : Dirac D) : dᵀᴰ = (d†ᴰ)ᶜᴰ :=
  (conj_adj d).symm

/-- A and C commute (both composites are `ᵀᴰ`). CoqQ `dirac.v:910-937`. -/
theorem adj_conj_comm (d : Dirac D) : (dᶜᴰ)†ᴰ = (d†ᴰ)ᶜᴰ := by
  rw [adj_conj, conj_adj]

/-! ## D-7: additivity over sums (CoqQ `dirac.v:942-960`-area) -/

/-- `†ᴰ` is additive over finite sums. -/
theorem adj_sum {ι : Type*} (s : Finset ι) (f : ι → Dirac D) :
    (∑ i ∈ s, f i)†ᴰ = ∑ i ∈ s, (f i)†ᴰ := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, adj_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, adj_add, ih]

/-- `ᶜᴰ` is additive over finite sums. -/
theorem conj_sum {ι : Type*} (s : Finset ι) (f : ι → Dirac D) :
    (∑ i ∈ s, f i)ᶜᴰ = ∑ i ∈ s, (f i)ᶜᴰ := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, conj_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, conj_add, ih]

/-- `ᵀᴰ` is additive over finite sums. -/
theorem transpose_sum {ι : Type*} (s : Finset ι) (f : ι → Dirac D) :
    (∑ i ∈ s, f i)ᵀᴰ = ∑ i ∈ s, (f i)ᵀᴰ := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, transpose_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, transpose_add, ih]

/-! ## D-7: (anti-)multiplicativity (CoqQ `adjdM:964`, `adjdT:969`,
`adjdG:975` and the `ᶜ`/`ᵀ` versions, `dirac.v:916-1010`) -/

/-- Interchange the two index pairs of a fourfold block sum. -/
private theorem sum₄_swap_pairs {M : Type*} [AddCommMonoid M]
    (f : Finset L → Finset L → Finset L → Finset L → M) :
    ∑ a : Finset L, ∑ b : Finset L, ∑ c : Finset L, ∑ e : Finset L, f a b c e =
      ∑ c : Finset L, ∑ e : Finset L, ∑ a : Finset L, ∑ b : Finset L,
        f a b c e := by
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun c _ => ?_)
  exact (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm

/-- `†ᴰ` anti-distributes over `∘ᴰ`. CoqQ `adjdM` (`dirac.v:964`). -/
theorem adj_comp (d₁ d₂ : Dirac D) : (d₁ ∘ᴰ d₂)†ᴰ = d₂†ᴰ ∘ᴰ d₁†ᴰ :=
  ext fun _ _ => by
    simp only [adj_apply, comp_apply, map_sum, LinearMap.adjoint_comp]

/-- `†ᴰ` distributes over `⊗ᴰ` (no swap: `⊗ᴰ` is commutative anyway).
CoqQ `adjdT` (`dirac.v:969`). -/
theorem adj_tensor (d₁ d₂ : Dirac D) : (d₁ ⊗ᴰ d₂)†ᴰ = d₁†ᴰ ⊗ᴰ d₂†ᴰ := by
  rw [tensor_def, tensor_def]
  simp only [adj_sum, adj_ofBlock, adjoint_tenf, adj_apply]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_comm

/-- `†ᴰ` anti-distributes over `·ᴰ`. CoqQ `adjdG` (`dirac.v:975`). -/
theorem adj_dot (d₁ d₂ : Dirac D) : (d₁ ·ᴰ d₂)†ᴰ = d₂†ᴰ ·ᴰ d₁†ᴰ := by
  rw [dot_def, dot_def]
  simp only [adj_sum, adj_ofBlock, adjoint_dotf, adj_apply]
  conv_lhs => rw [sum₄_swap_pairs, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_comm

/-- `ᶜᴰ` is multiplicative for `∘ᴰ` (*no* swap). CoqQ `conjdM`
(`dirac.v:916-1010`). -/
theorem conj_comp (d₁ d₂ : Dirac D) : (d₁ ∘ᴰ d₂)ᶜᴰ = d₁ᶜᴰ ∘ᴰ d₂ᶜᴰ :=
  ext fun _ _ => by
    simp only [conj_apply, comp_apply, conjLM_sum, conjLM_comp]

/-- `ᶜᴰ` is multiplicative for `⊗ᴰ`. CoqQ `conjdT` (`dirac.v:916-1010`). -/
theorem conj_tensor (d₁ d₂ : Dirac D) : (d₁ ⊗ᴰ d₂)ᶜᴰ = d₁ᶜᴰ ⊗ᴰ d₂ᶜᴰ := by
  rw [tensor_def, tensor_def]
  simp only [conj_sum, conj_ofBlock, conjLM_tenf, conj_apply]

/-- `ᶜᴰ` is multiplicative for `·ᴰ` (*no* swap). CoqQ `conjdG`
(`dirac.v:916-1010`). -/
theorem conj_dot (d₁ d₂ : Dirac D) : (d₁ ·ᴰ d₂)ᶜᴰ = d₁ᶜᴰ ·ᴰ d₂ᶜᴰ := by
  rw [dot_def, dot_def]
  simp only [conj_sum, conj_ofBlock, conjLM_dotf, conj_apply]

/-- `ᵀᴰ` anti-distributes over `∘ᴰ` (swaps, like `†ᴰ`). CoqQ `trdM`
(`dirac.v:916-1010`). -/
theorem transpose_comp (d₁ d₂ : Dirac D) : (d₁ ∘ᴰ d₂)ᵀᴰ = d₂ᵀᴰ ∘ᴰ d₁ᵀᴰ := by
  rw [← conj_adj, adj_comp, conj_comp, conj_adj, conj_adj]

/-- `ᵀᴰ` distributes over `⊗ᴰ`. CoqQ `trdT` (`dirac.v:916-1010`). -/
theorem transpose_tensor (d₁ d₂ : Dirac D) :
    (d₁ ⊗ᴰ d₂)ᵀᴰ = d₁ᵀᴰ ⊗ᴰ d₂ᵀᴰ := by
  rw [← conj_adj, adj_tensor, conj_tensor, conj_adj, conj_adj]

/-- `ᵀᴰ` anti-distributes over `·ᴰ` (swaps, like `†ᴰ`). CoqQ `trdG`
(`dirac.v:916-1010`). -/
theorem transpose_dot (d₁ d₂ : Dirac D) : (d₁ ·ᴰ d₂)ᵀᴰ = d₂ᵀᴰ ·ᴰ d₁ᵀᴰ := by
  rw [← conj_adj, adj_dot, conj_dot, conj_adj, conj_adj]

/-! ## D-7: constructors under the unaries (CoqQ `dirac.v:916-1010`) -/

/-- `†ᴰ` turns kets into bras. CoqQ `adjd_ket` (`dirac.v:916-1010`). -/
@[simp, dirac_simps]
theorem adj_ket (v : HS D S) : (∣v⟩ᴰ : Dirac D)†ᴰ = ⟨v∣ᴰ := by
  rw [ket, adj_ofBlock, adjoint_toKetM, bra]

/-- `†ᴰ` turns bras into kets. CoqQ `adjd_bra` (`dirac.v:916-1010`). -/
@[simp, dirac_simps]
theorem adj_bra (v : HS D S) : (⟨v∣ᴰ : Dirac D)†ᴰ = ∣v⟩ᴰ := by
  rw [bra, adj_ofBlock, adjoint_toBraM, ket]

/-- `†ᴰ` conjugates scalars. CoqQ `adjd_num` (`dirac.v:916-1010`). -/
@[simp, dirac_simps]
theorem adj_num (c : ℂ) : (num D c)†ᴰ = num D (star c) := by
  rw [num, adj_ofBlock, adjoint_toScalarM, num]

/-- `†ᴰ` fixes identities. CoqQ `adjd1` (`dirac.v:916-1010`). -/
@[simp, dirac_simps]
theorem adj_one : (one D S)†ᴰ = one D S := by
  rw [one, adj_ofBlock, LinearMap.adjoint_one]

/-- `ᶜᴰ` conjugates the ket vector. CoqQ `conjd_ket` (`dirac.v:916-1010`). -/
@[simp, dirac_simps]
theorem conj_ket (v : HS D S) : (∣v⟩ᴰ : Dirac D)ᶜᴰ = ∣conjV v⟩ᴰ := by
  rw [ket, conj_ofBlock, conjLM_toKetM, ket]

/-- `ᶜᴰ` conjugates the bra vector. CoqQ `conjd_bra` (`dirac.v:916-1010`). -/
@[simp, dirac_simps]
theorem conj_bra (v : HS D S) : (⟨v∣ᴰ : Dirac D)ᶜᴰ = ⟨conjV v∣ᴰ := by
  rw [bra, conj_ofBlock, conjLM_toBraM, bra]

/-- `ᶜᴰ` conjugates scalars. CoqQ `conjd_num` (`dirac.v:916-1010`). -/
@[simp, dirac_simps]
theorem conj_num (c : ℂ) : (num D c)ᶜᴰ = num D (star c) := by
  rw [num, conj_ofBlock, conjLM_toScalarM, num]

/-- `ᶜᴰ` fixes identities. CoqQ `conjd1` (`dirac.v:916-1010`). -/
@[simp, dirac_simps]
theorem conj_one : (one D S)ᶜᴰ = one D S := by
  rw [one, conj_ofBlock, conjLM_one]

/-- `ᵀᴰ` turns kets into conjugated bras. CoqQ `trd_ket`
(`dirac.v:916-1010`). -/
@[simp, dirac_simps]
theorem transpose_ket (v : HS D S) : (∣v⟩ᴰ : Dirac D)ᵀᴰ = ⟨conjV v∣ᴰ := by
  rw [ket, transpose_ofBlock, transposeLM_toKetM, bra]

/-- `ᵀᴰ` turns bras into conjugated kets. CoqQ `trd_bra`
(`dirac.v:916-1010`). -/
@[simp, dirac_simps]
theorem transpose_bra (v : HS D S) : (⟨v∣ᴰ : Dirac D)ᵀᴰ = ∣conjV v⟩ᴰ := by
  rw [bra, transpose_ofBlock, transposeLM_toBraM, ket]

/-- `ᵀᴰ` fixes scalars (`ᵀ = ᶜ ∘ †`, the two stars cancel). CoqQ `trd_num`
(`dirac.v:916-1010`). -/
@[simp, dirac_simps]
theorem transpose_num (c : ℂ) : (num D c)ᵀᴰ = num D c := by
  rw [num, transpose_ofBlock, transposeLM_toScalarM]

/-- `ᵀᴰ` fixes identities. CoqQ `trd1` (`dirac.v:916-1010`). -/
@[simp, dirac_simps]
theorem transpose_one : (one D S)ᵀᴰ = one D S := by
  rw [one, transpose_ofBlock, transposeLM_one]

end Dirac

end Qhl
