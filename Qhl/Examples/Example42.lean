import Qhl.Dirac.Laws
import Qhl.Examples.Bell

/-!
# M5 acceptance test: the paper's Example 4.2

`A[S] ∣Φ⟩ = Aᵀ[T] ∣Φ⟩` — an operator acting on one half of the maximally
entangled state `∣Φ⟩ = ∑ k, ∣k⟩_S ⊗ ∣k⟩_T` equals its transpose acting on the
other half (CoqQ paper §4.2; `dirac.v`-adjacent).

Fixture: two disjoint registers `S T : Finset L` whose classical states are
identified by an equivalence `e : QIdx D S ≃ QIdx D T` (the fully general
form; the two-qubit Bell fixture of `Qhl.Examples.Bell` instantiates it at
the end of this file).

* transport layer: `transportV e` (relabelling of vectors), `transportEnd e`
  (conjugation of operators), entry lemmas
* `maxEnt D e` — the (unnormalized) maximally entangled state as a labelled
  Dirac ket on `S ∪ T`
* `ofBlock_dot_maxEnt_left/right` — the two D-L rewrite chains pulling an
  operator through `·ᴰ` onto one tensor factor (D-L8 + `ofBlock_dot_ket`)
* `maxEnt_transfer` — engine form, for any `B` whose matrix along `e` is the
  transpose of `A`'s
* `maxEnt_transpose` — the headline `A[S] ∣Φ⟩ = Aᵀ[T] ∣Φ⟩`
-/

namespace Qhl.Example42

open Finset Qhl.Dirac
open scoped ComplexInnerProductSpace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L] (D : L → Type*)
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] {S T : Finset L}

/-! ## Transport along a relabelling of classical states -/

/-- Entries of the transpose are the transposed entries (layer-1 support;
matrix-entry mirror of CoqQ `tr_lfun`). -/
theorem transposeLM_deltav_apply (f : LinM D S T) (k : QIdx D T)
    (l : QIdx D S) : transposeLM f (deltav D k) l = f (deltav D l) k := by
  rw [← adjoint_conjLM, adjoint_deltav_apply, conjLM_apply, conjV_deltav,
    conjV_apply, star_star]

/-- Relabelling of vectors along an identification `e` of classical states,
as a labelled linear map: `∣k⟩_S ↦ ∣e k⟩_T`. -/
noncomputable def transportV (e : QIdx D S ≃ QIdx D T) : LinM D S T :=
  ∑ k, outerLM (deltav D (e k)) (deltav D k)

/-- `transportV` relabels the computational basis. -/
theorem transportV_deltav (e : QIdx D S ≃ QIdx D T) (k : QIdx D S) :
    transportV D e (deltav D k) = deltav D (e k) := by
  have hz : ∀ l, l ≠ k →
      outerLM (deltav D (e l)) (deltav D l) (deltav D k) = 0 := fun l hl => by
    rw [outerLM_apply, dv_dot, if_neg hl, zero_smul]
  rw [transportV, LinearMap.sum_apply, Fintype.sum_eq_single k hz,
    outerLM_apply, dv_dot, if_pos rfl, one_smul]

/-- `transportV` relabels coefficients. -/
theorem cdv_transportV (e : QIdx D S ≃ QIdx D T) (w : HS D S)
    (l : QIdx D S) : cdv D (e l) (transportV D e w) = cdv D l w := by
  have hz : ∀ m, m ≠ l →
      outerLM (deltav D (e m)) (deltav D m) w (e l) = 0 := fun m hm => by
    rw [outerLM_apply, PiLp.smul_apply, deltav_apply,
      if_neg fun h => hm (e.injective h).symm, smul_zero]
  rw [cdv_apply, cdv_apply, transportV, LinearMap.sum_apply, HS_sum_apply,
    Fintype.sum_eq_single l hz, outerLM_apply, inner_deltav, PiLp.smul_apply,
    deltav_apply, if_pos rfl, smul_eq_mul, mul_one]

/-- Transport of a square labelled operator along `e`: conjugation
`A ↦ V_e ∘ A ∘ V_e⁻¹` (`Aᵀ[T]` in the paper is
`transportEnd D e (transposeLM A)`). -/
noncomputable def transportEnd (e : QIdx D S ≃ QIdx D T) (A : EndM D S) :
    EndM D T :=
  transportV D e ∘ₗ A ∘ₗ transportV D e.symm

/-- The matrix of the transported transpose, along `e`: it is the transposed
matrix of `A`. -/
theorem transportEnd_transpose_entry (e : QIdx D S ≃ QIdx D T) (A : EndM D S)
    (k l : QIdx D S) :
    cdv D (e l) (transportEnd D e (transposeLM A) (deltav D (e k)))
      = cdv D k (A (deltav D l)) := by
  rw [transportEnd]
  simp only [LinearMap.comp_apply]
  rw [transportV_deltav, Equiv.symm_apply_apply, cdv_transportV, cdv_apply,
    cdv_apply, transposeLM_deltav_apply]

/-! ## The maximally entangled state -/

variable (hST : Disjoint S T) (e : QIdx D S ≃ QIdx D T)

/-- The (unnormalized) maximally entangled state
`∣Φ⟩ = ∑ k, ∣k⟩_S ⊗ ∣e k⟩_T`, as a labelled Dirac expression. -/
noncomputable def maxEnt : Dirac D :=
  ∑ k : QIdx D S, ∣tenv D (deltav D k) (deltav D (e k))⟩ᴰ

/-- `∣Φ⟩` is a wf ket on the joint register. -/
theorem maxEnt_isKetOn : IsKetOn (S ∪ T) (maxEnt D e) :=
  WFAt.sum fun _ _ => wf_ket _

include hST in
/-- `A[S]` pulled onto the left tensor factor of `∣Φ⟩`: a D-L chain
(`ket_tensor_ket`, D-L8 `dot_tensor_ll`, `ofBlock_dot_ket`). -/
theorem ofBlock_dot_maxEnt_left (A : EndM D S) :
    (⌈A⌉ᴰ : Dirac D) ·ᴰ maxEnt D e
      = ∑ k, (∣A (deltav D k)⟩ᴰ : Dirac D) ⊗ᴰ ∣deltav D (e k)⟩ᴰ := by
  rw [maxEnt, dot_sum_right]
  exact Finset.sum_congr rfl fun k _ => by
    rw [← ket_tensor_ket,
      dot_tensor_ll (wf_ofBlock A) (wf_ket _) (wf_ket _) hST hST,
      ofBlock_dot_ket]

include hST in
/-- `B[T]` pulled onto the right tensor factor of `∣Φ⟩` (mirror chain, D-L8
`dot_tensor_lr`). -/
theorem ofBlock_dot_maxEnt_right (B : EndM D T) :
    (⌈B⌉ᴰ : Dirac D) ·ᴰ maxEnt D e
      = ∑ k, (∣deltav D k⟩ᴰ : Dirac D) ⊗ᴰ ∣B (deltav D (e k))⟩ᴰ := by
  rw [maxEnt, dot_sum_right]
  exact Finset.sum_congr rfl fun k _ => by
    rw [← ket_tensor_ket,
      dot_tensor_lr (wf_ofBlock B) (wf_ket _) (wf_ket _) hST.symm hST.symm,
      ofBlock_dot_ket]

include hST in
/-- **Example 4.2**, engine form: if the matrix of `B` along `e` is the
transposed matrix of `A`, then `A[S] ∣Φ⟩ = B[T] ∣Φ⟩`. Both sides are pulled
onto one tensor factor by the D-L chains above, expanded in the computational
basis, and the two summation indices are swapped. -/
theorem maxEnt_transfer (A : EndM D S) (B : EndM D T)
    (hAB : ∀ k l : QIdx D S,
      cdv D (e l) (B (deltav D (e k))) = cdv D k (A (deltav D l))) :
    (⌈A⌉ᴰ : Dirac D) ·ᴰ maxEnt D e = (⌈B⌉ᴰ : Dirac D) ·ᴰ maxEnt D e :=
  calc (⌈A⌉ᴰ : Dirac D) ·ᴰ maxEnt D e
      = ∑ k, ∑ l, cdv D l (A (deltav D k)) •
          ((∣deltav D l⟩ᴰ : Dirac D) ⊗ᴰ ∣deltav D (e k)⟩ᴰ) := by
        rw [ofBlock_dot_maxEnt_left D hST e A]
        refine Finset.sum_congr rfl fun k _ => ?_
        conv_lhs => rw [dec_dv D (A (deltav D k))]
        rw [ket_sum, tensor_sum_left]
        exact Finset.sum_congr rfl fun l _ => by
          rw [ket_smul, tensor_smul_left]
    _ = ∑ k, ∑ l, cdv D k (A (deltav D l)) •
          ((∣deltav D k⟩ᴰ : Dirac D) ⊗ᴰ ∣deltav D (e l)⟩ᴰ) := Finset.sum_comm
    _ = (⌈B⌉ᴰ : Dirac D) ·ᴰ maxEnt D e := by
        rw [ofBlock_dot_maxEnt_right D hST e B]
        refine Eq.symm (Finset.sum_congr rfl fun k _ => ?_)
        conv_lhs => rw [dec_dv D (B (deltav D (e k)))]
        rw [ket_sum, tensor_sum_right]
        exact (Fintype.sum_equiv e _ _ fun l => by
          rw [ket_smul, tensor_smul_right, hAB k l]).symm

include hST in
/-- **Example 4.2** (paper §4.2), headline form:
`A[S] ∣Φ⟩ = Aᵀ[T] ∣Φ⟩` — acting on one half of the maximally entangled state
equals acting on the other half with the transported transpose. -/
theorem maxEnt_transpose (A : EndM D S) :
    (⌈A⌉ᴰ : Dirac D) ·ᴰ maxEnt D e
      = (⌈transportEnd D e (transposeLM A)⌉ᴰ : Dirac D) ·ᴰ maxEnt D e :=
  maxEnt_transfer D hST e A _ (transportEnd_transpose_entry D e A)

/-! ## Instantiation at the two-qubit Bell fixture (`Qhl.Examples.Bell`) -/

/-- The relabelling `{false} ≃ {true}` of the classical states of the
two-qubit fixture. -/
def flip01 : QIdx Bell.Qubit {false} ≃ QIdx Bell.Qubit {true} where
  toFun k := fun _ => k ⟨false, Finset.mem_singleton_self false⟩
  invFun l := fun _ => l ⟨true, Finset.mem_singleton_self true⟩
  left_inv k := funext fun i => by
    obtain ⟨b, hb⟩ := i
    obtain rfl := Finset.mem_singleton.mp hb
    rfl
  right_inv l := funext fun i => by
    obtain ⟨b, hb⟩ := i
    obtain rfl := Finset.mem_singleton.mp hb
    rfl

/-- Example 4.2 on the Bell fixture: any single-qubit operator crosses the
(unnormalized) Bell state as its transpose on the partner qubit. -/
example (A : EndM Bell.Qubit {false}) :
    (⌈A⌉ᴰ : Dirac Bell.Qubit) ·ᴰ maxEnt Bell.Qubit flip01
      = ⌈transportEnd Bell.Qubit flip01 (transposeLM A)⌉ᴰ ·ᴰ
          maxEnt Bell.Qubit flip01 :=
  maxEnt_transpose Bell.Qubit Bell.disj flip01 A

end Qhl.Example42
