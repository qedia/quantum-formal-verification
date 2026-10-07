import Qhl.Logic.Subroutine
import Qhl.Logic.ProdChain

/-! Product-state endpoints for the derived subroutine frame rule. -/
namespace Qhl
open Finset

variable {L' L : Type*} [Fintype L'] [DecidableEq L'] [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]

/-- Relabelling a product state relabels each of its factors. -/
theorem embHSp_prodV (emb : L' ↪ L) (S : Finset L')
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    embHSp D emb S (prodV (fun i => D (emb i)) (W := S) (fun i => ψ (emb i)))
      = prodV D (W := S.map emb) ψ := by
  apply PiLp.ext
  intro x
  let m : ∀ i, D i := fun i => if hi : i ∈ S.map emb then x ⟨i, hi⟩ else default
  have hx : x = fun i : ↥(S.map emb) => m i := by
    funext i
    dsimp only [m]
    rw [dif_pos i.2]
  rw [hx]
  change prodV (fun i => D (emb i)) (W := S) (fun i => ψ (emb i))
      ((embIdxEquiv D emb S).symm (fun i => m i)) = _
  rw [embIdxEquiv_symm_restrict, prodV_apply, prodV_apply,
    ← Equiv.prod_comp (embCellEquiv emb S)]
  rfl

/-- Framing a product assertion reconstructs the product assertion on all cells. -/
theorem Assn.embFrame_prodA {σT : Type*} (emb : L' ↪ L)
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) (hψ : ∀ i, ‖ψ i‖ = 1) :
    (prodA (σT := σT) (fun i => D (emb i)) (fun i => ψ (emb i))
      (fun i => hψ (emb i))).embFrame (emb := emb)
      (outerLM (prodV D (W := univ \ embRange emb) ψ)
        (prodV D (W := univ \ embRange emb) ψ))
      (isEffect_outerLM_self (norm_prodV_eq_one ψ hψ)) = prodA D ψ hψ := by
  apply Assn.ext
  funext σ
  rw [Assn.embFrame_op, prodA_op, prodA_op]
  change castF D _ _ (tenf D
    ((embHSp D emb univ).toLinearEquiv.conj (outerLM _ _)) _) = _
  rw [conj_isometryEquiv_outerLM, embHSp_prodV, tenf_outerLM]
  change (castH D (embRange_union_sdiff emb)).toLinearEquiv.conj (outerLM _ _) = _
  rw [conj_isometryEquiv_outerLM, ← prodV_split D (subset_univ (embRange emb)) ψ]

/-- A product-state triple may be placed on any embedded register, preserving
all product factors outside that register. -/
theorem DerivTot.onReg_prodA {σT : Type*} (emb : L' ↪ L)
    (ψ φ : ∀ i, EuclideanSpace ℂ (D i))
    (hψ : ∀ i, ‖ψ i‖ = 1) (hφ : ∀ i, ‖φ i‖ = 1)
    (hout : ∀ i ∈ univ \ embRange emb, ψ i = φ i)
    {P : Prog σT (fun i => D (emb i))}
    (h : DerivTot
      (prodA (fun i => D (emb i)) (fun i => ψ (emb i)) (fun i => hψ (emb i))) P
      (prodA (fun i => D (emb i)) (fun i => φ (emb i)) (fun i => hφ (emb i)))) :
    DerivTot (prodA D ψ hψ) (P.onReg emb) (prodA D φ hφ) := by
  have hv : prodV D (W := univ \ embRange emb) ψ
      = prodV D (W := univ \ embRange emb) φ := prodV_congr D hout
  have hf := DerivTot.embFrame_onReg (emb := emb)
    (R := outerLM (prodV D (W := univ \ embRange emb) ψ)
      (prodV D (W := univ \ embRange emb) ψ))
    (hR := isEffect_outerLM_self (norm_prodV_eq_one ψ hψ)) h
  rw [Assn.embFrame_prodA] at hf
  simpa only [hv, Assn.embFrame_prodA] using hf

end Qhl
