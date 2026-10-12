import Qhl.Logic.InitBlock
import Qhl.Logic.WpChain

namespace Qhl
open Finset
variable {L L₁ L₂ : Type*} [Fintype L] [DecidableEq L]
  [Fintype L₁] [DecidableEq L₁] [Fintype L₂] [DecidableEq L₂]

private theorem idx_restrict {k : ℕ} (r : Reg L k) (f : L → Bool) :
    r.idxEquiv (QubitCells L) (fun j => f (r j)) =
      fun i : ↥r.sig => f i := by
  funext i
  change f (r (r.equivSig.symm i)) = f i
  rw [r.apply_equivSig_symm]

private theorem regLift_entry {k : ℕ} (r : Reg L k)
    (A : TSpace (QubitCells L) r.toFun →ₗ[ℂ] TSpace (QubitCells L) r.toFun)
    (f g : L → Bool) :
    regLift r A (deltav (QubitCells L) (qbIdx L f)) (qbIdx L g) =
      A (EuclideanSpace.single (fun j => f (r j)) 1) (fun j => g (r j)) *
        (if ∀ i, i ∉ r.sig → g i = f i then 1 else 0) := by
  rw [regLift_deltav_apply]
  have hf : QIdx.res (QubitCells L) (subset_univ r.sig) (qbIdx L f) =
      r.idxEquiv (QubitCells L) (fun j => f (r j)) := (idx_restrict r f).symm
  have hg : QIdx.res (QubitCells L) (subset_univ r.sig) (qbIdx L g) =
      r.idxEquiv (QubitCells L) (fun j => g (r j)) := (idx_restrict r g).symm
  rw [hf, hg, Reg.op_deltav_apply]
  congr 1
  congr 1
  apply propext
  constructor
  · intro h i hi
    exact congrFun h ⟨i, mem_sdiff.mpr ⟨mem_univ _, hi⟩⟩
  · intro h
    funext i
    exact h i (mem_sdiff.mp i.property).2

/-- Placing a register in the left summand is the system operator lift. -/
theorem regLift_inl_eq_sysLift {k : ℕ} (r : Reg L₁ k)
    (A : TSpace (QubitCells L₁) r.toFun →ₗ[ℂ] TSpace (QubitCells L₁) r.toFun) :
    regLift (D := QubitCells (L₁ ⊕ L₂))
      ⟨fun j => Sum.inl (r j), Sum.inl_injective.comp r.inj⟩ A =
      sysLift (L₂ := L₂) (regLift r A) := by
  apply linM_ext (QubitCells (L₁ ⊕ L₂))
  intro f
  let f' : L₁ ⊕ L₂ → Bool := fun i => f ⟨i, mem_univ i⟩
  have hf : f = qbIdx (L₁ ⊕ L₂) f' := rfl
  rw [hf]
  conv_rhs => rw [deltav_eq_ancEmbed, sysLift_apply_emb]
  apply PiLp.ext
  intro g
  let g' : L₁ ⊕ L₂ → Bool := fun i => g ⟨i, mem_univ i⟩
  have hg : g = qbIdx (L₁ ⊕ L₂) g' := rfl
  rw [hg]
  rw [regLift_entry, ancEmbed_apply, regLift_entry]
  have hsig (i : L₁) : Sum.inl i ∈
      (Reg.mk (fun j => (Sum.inl (r j) : L₁ ⊕ L₂))
        (Sum.inl_injective.comp r.inj)).sig ↔ i ∈ r.sig := by
    simp only [Reg.mem_sig, Reg.coe_mk, Sum.inl.injEq]
  have hanc (i : L₂) : Sum.inr i ∉
      (Reg.mk (fun j => (Sum.inl (r j) : L₁ ⊕ L₂)) (Sum.inl_injective.comp r.inj)).sig := by
    simp only [Reg.mem_sig, Reg.coe_mk, Sum.inl_ne_inr, exists_false, not_false_eq_true]
  simp +instances only [qbIdx, Reg.coe_mk]
  by_cases ha : (fun a => g' (Sum.inr a)) = (fun a => f' (Sum.inr a))
  · erw [if_pos ha]
    congr 1
    congr 1
    apply propext
    constructor
    · intro h i hi
      exact h (Sum.inl i) (fun hh => hi ((hsig i).mp hh))
    · intro h i hi
      cases i with
      | inl i => exact h i (fun hh => hi ((hsig i).mpr hh))
      | inr i => exact congrFun ha i
  · erw [if_neg ha]
    have h : ¬ (∀ i, i ∉ (Reg.mk (fun j => (Sum.inl (r j) : L₁ ⊕ L₂))
        (Sum.inl_injective.comp r.inj)).sig → g' i = f' i) := by
      intro h
      exact ha (funext fun i => h (Sum.inr i) (hanc i))
    rw [if_neg h, mul_zero]
end Qhl

namespace Qhl
open Finset
variable {L₁ L₂ : Type*} [Fintype L₁] [DecidableEq L₁] [Fintype L₂] [DecidableEq L₂]

theorem sysLift_comp (A B : EndM (QubitCells L₁) univ) :
    sysLift (L₂ := L₂) (A ∘ₗ B) = sysLift (L₂ := L₂) A ∘ₗ sysLift (L₂ := L₂) B := by
  apply linM_ext (QubitCells (L₁ ⊕ L₂))
  intro f
  have hf : f = qbIdx (L₁ ⊕ L₂) (fun i => f ⟨i, mem_univ i⟩) := rfl
  rw [hf]
  rw [deltav_eq_ancEmbed]
  simp only [LinearMap.comp_apply, sysLift_apply_emb]

theorem adjoint_sysLift (A : EndM (QubitCells L₁) univ) :
    LinearMap.adjoint (sysLift (L₂ := L₂) A) = sysLift (L₂ := L₂) (LinearMap.adjoint A) := by
  simp only [sysLift, map_sum, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint,
    LinearMap.comp_assoc]
end Qhl

#print axioms Qhl.regLift_inl_eq_sysLift
#print axioms Qhl.sysLift_comp
#print axioms Qhl.adjoint_sysLift

namespace Qhl
open Finset
variable {L₁ L₂ : Type*} [Fintype L₁] [DecidableEq L₁] [Fintype L₂] [DecidableEq L₂]

theorem sysLift_chainOp {ι : Type*} (li : List ι)
    (G : ι → EndM (QubitCells L₁) univ) :
    chainOp li (fun i => sysLift (L₂ := L₂) (G i)) = sysLift (L₂ := L₂) (chainOp li G) := by
  induction li with
  | nil => simp only [chainOp_nil, sysLift_one]
  | cons i li ih => rw [chainOp_cons, chainOp_cons, sysLift_comp, ih]
end Qhl
#print axioms Qhl.sysLift_chainOp
