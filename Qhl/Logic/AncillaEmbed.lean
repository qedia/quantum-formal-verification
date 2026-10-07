import Qhl.Logic.Frame
import Qhl.Logic.ForSeqRule
import Qhl.Gate.ControlledU
import Qhl.Logic.UnitaryFull
import Qhl.Logic.WpChain
import Qhl.Register.PauliString
import Qhl.Register.Qubits

/-!
# The ancilla-block embedding of a qubit world, and its gate collapses

The generic layer an LCU-style circuit needs: the world is a **sum**
`L₁ ⊕ L₂` of qubit cells (`L₁` the system block, `L₂` the ancilla block), the
ancilla block is in a computational basis state `e : L₂ → Bool`, and the
system block carries an **arbitrary** (possibly entangled) state `w`.  The
linear map `ancEmbed e : HS L₁ →ₗ HS (L₁ ⊕ L₂)` produces exactly those
states, and every gate of such a circuit collapses on them:

* `qubitHS_expand` — a state of a qubit world is the sum of its computational
  coordinates (`deltav` basis expansion), with the inner-product form
  `inner_qubitHS_expand`;
* `regLift_pairGate_prodV_sum` — the **sum-output** form of the two-cell frame
  bridge `regLift_pairGate_prodV` (`Qhl/Logic/Frame.lean`): the gate may send
  the named product pair to a *linear combination* of product pairs;
* `gateAt_deltav_expand` / `prodV_update_addPS` — one-cell gates on basis
  kets, in expansion form;
* `ancEmbed` with `ancEmbed_deltav`, `ancEmbed_expand`, `inner_ancEmbed`,
  `norm_ancEmbed`, `adjoint_ancEmbed_comp` — the embedding is an isometry and
  embeddings at distinct ancilla patterns are orthogonal;
* the **gate collapses**: a system gate commutes past the embedding
  (`gateAt_inl_ancEmbed`), a one-cell ancilla gate collapses to its basis
  action (`gateAt_inr_ancEmbed`), a two-cell ancilla gate collapses to its
  expanded basis action (`pairGate_anc_ancEmbed`), and a controlled gate with
  ancilla control and system target fires exactly when the stored control bit
  is set (`pairGate_ctrl_ancEmbed`);
* `Assn.ofStateFam` / `DerivTot.unitary_stateFam` — the store-parameterized
  form of `DerivTot.unitary_state` (`Qhl/Logic/UnitaryFull.lean`): gates whose
  unitary is computed from the classical store, on a store-indexed family of
  pure states.  Built from the `DerivTot` constructors `.unitary` and
  `.conseq` alone — no new rule primitive.

Nothing here names a particular program or gate; everything is generic in the
two label types, the classical store and the gates.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

/-! ## §1. Basis expansion on a qubit world -/

section Expand

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- `qbIdx` is injective: total bit vectors index distinct classical states. -/
theorem qbIdx_injective : Function.Injective (qbIdx L) := by
  intro f g h
  funext i
  exact congrFun h ⟨i, mem_univ i⟩

/-- The total-bit-vector view of a qubit world's classical states. -/
def qbEquiv (L : Type*) [Fintype L] [DecidableEq L] :
    (L → Bool) ≃ QIdx (QubitCells L) (univ : Finset L) where
  toFun := qbIdx L
  invFun k := fun i => k ⟨i, mem_univ i⟩
  left_inv f := rfl
  right_inv k := qbIdx_eq k

/-- **Basis expansion**: a state of the qubit world is the sum of its
computational coordinates. -/
theorem qubitHS_expand (w : HS (QubitCells L) (univ : Finset L)) :
    w = ∑ f : L → Bool, w (qbIdx L f) • deltav (QubitCells L) (qbIdx L f) := by
  refine PiLp.ext fun g => ?_
  rw [HS_sum_apply]
  rw [Finset.sum_eq_single (fun i => g ⟨i, mem_univ i⟩)]
  · rw [PiLp.smul_apply, qbIdx_eq, deltav_apply, if_pos rfl, smul_eq_mul, mul_one]
  · intro f _ hf
    rw [PiLp.smul_apply, deltav_apply, if_neg, smul_eq_mul, mul_zero]
    intro hc
    exact hf (qbIdx_injective (by rw [← hc, qbIdx_eq]))
  · intro hc
    exact absurd (mem_univ _) hc

/-- The inner product of a qubit world, as a sum over total bit vectors. -/
theorem inner_qubitHS_expand (w w' : HS (QubitCells L) (univ : Finset L)) :
    (⟪w, w'⟫ : ℂ)
      = ∑ f : L → Bool, (starRingEnd ℂ) (w (qbIdx L f)) * w' (qbIdx L f) := by
  rw [PiLp.inner_apply, ← Equiv.sum_comp (qbEquiv L)]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [RCLike.inner_apply]
  exact mul_comm _ _

/-- A one-qubit vector expanded in the two basis kets. -/
theorem qubit_expand (v : 𝕢) :
    v = v false • EuclideanSpace.single false 1 + v true • EuclideanSpace.single true 1 := by
  refine PiLp.ext fun b => ?_
  cases b <;>
    simp [EuclideanSpace.single_apply]

end Expand

/-! ## §2. One-cell gates on basis kets, expansion form -/

section OneCell

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]

/-- Adding in one slot of a per-cell product state adds the product states
(the companion of `prodV_update_smulPS`). -/
theorem prodV_update_addPS {W : Finset L} (a : L) (ha : a ∈ W)
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) (u v : EuclideanSpace ℂ (D a)) :
    prodV D (W := W) (Function.update ψ a (u + v))
      = prodV D (W := W) (Function.update ψ a u)
        + prodV D (W := W) (Function.update ψ a v) := by
  refine PiLp.ext fun l => ?_
  rw [PiLp.add_apply, prodV_apply, prodV_apply, prodV_apply]
  set i0 : ↥W := ⟨a, ha⟩ with hi0
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0)]
  have e1 : Function.update ψ a (u + v) (i0 : L) (l i0)
      = Function.update ψ a u (i0 : L) (l i0) + Function.update ψ a v (i0 : L) (l i0) := by
    show Function.update ψ a (u + v) a (l i0)
      = Function.update ψ a u a (l i0) + Function.update ψ a v a (l i0)
    rw [Function.update_self, Function.update_self, Function.update_self, PiLp.add_apply]
  have e2 : ∀ (z : EuclideanSpace ℂ (D a)) (i : ↥W), i ∈ Finset.univ.erase i0 →
      Function.update ψ a z (i : L) (l i) = ψ (i : L) (l i) := fun z i hi => by
    have hne : (i : L) ≠ a := fun hc => (Finset.mem_erase.mp hi).1 (Subtype.ext hc)
    rw [Function.update_of_ne hne]
  rw [e1, Finset.prod_congr rfl (e2 (u + v)), Finset.prod_congr rfl (e2 u),
    Finset.prod_congr rfl (e2 v), add_mul]

/-- **A one-cell qubit gate on a basis ket, in expansion form**: the image is
the two-term combination given by the gate's column at the stored bit. -/
theorem gateAt_deltav_expand (a : L) (U : UnitaryOp 𝕢) (f : L → Bool) :
    gateAt L a U (deltav (QubitCells L) (qbIdx L f))
      = ∑ b : Bool, ((U : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single (f a) 1)) b •
          deltav (QubitCells L) (qbIdx L (Function.update f a b)) := by
  have h1 : deltav (QubitCells L) (qbIdx L f)
      = prodV (QubitCells L) (W := univ) (fun i => EuclideanSpace.single (f i) 1) :=
    (prodV_single (QubitCells L) f).symm
  rw [h1, gateAt_prodV]
  have h2 : (U : 𝕢 →ₗ[ℂ] 𝕢) ((fun i => (EuclideanSpace.single (f i) 1 :
        EuclideanSpace ℂ (QubitCells L i))) a)
      = (U : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single (f a) 1) := rfl
  rw [h2]
  conv_lhs => rw [qubit_expand ((U : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single (f a) 1))]
  rw [prodV_update_addPS (D := QubitCells L) a (mem_univ a),
    prodV_update_smulPS (QubitCells L) a (mem_univ a),
    prodV_update_smulPS (QubitCells L) a (mem_univ a),
    update_singleFamily, update_singleFamily, prodV_single, prodV_single,
    Fintype.sum_bool, add_comm]
  rfl

end OneCell

/-! ## §3. The sum-output two-cell frame bridge -/

section PairSum

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]

/-- **The sum-output form of the two-cell frame bridge**
`regLift_pairGate_prodV` (`Qhl/Logic/Frame.lean`): the gate hypothesis may
present the image of the named product pair as a **linear combination** of
product pairs, and the whole-world lift then produces the same combination of
updated product states, the complement framed in every summand. -/
theorem regLift_pairGate_prodV_sum {ι : Type*} (s : Finset ι) (a b : L) (hab : a ≠ b)
    (G : UnitaryOp (EuclideanSpace ℂ (D a × D b)))
    (c : ι → ℂ) (u : ι → EuclideanSpace ℂ (D a)) (v : ι → EuclideanSpace ℂ (D b))
    (ψ : ∀ i, EuclideanSpace ℂ (D i))
    (hG : (G : EuclideanSpace ℂ (D a × D b) →ₗ[ℂ] EuclideanSpace ℂ (D a × D b))
        (vpair (ψ a) (ψ b)) = ∑ i ∈ s, c i • vpair (u i) (v i)) :
    regLift (Reg.pair a b hab) (pairGate a b hab G) (prodV D (W := (univ : Finset L)) ψ)
      = ∑ i ∈ s, c i • prodV D (W := (univ : Finset L))
          (Function.update (Function.update ψ a (u i)) b (v i)) := by
  have h : (Reg.pair a b hab).sig ⊆ (univ : Finset L) := subset_univ _
  change liftF D h ((Reg.pair a b hab).op D
    (pairGate a b hab G : TSpace D (Reg.pair a b hab).toFun →ₗ[ℂ] _))
      (prodV D (W := (univ : Finset L)) ψ) = _
  rw [liftF_regOp_prodV]
  have hblock : (Reg.pair a b hab).op D
      (pairGate a b hab G : TSpace D (Reg.pair a b hab).toFun →ₗ[ℂ] _)
      (prodV D (W := (Reg.pair a b hab).sig) ψ)
      = ∑ i ∈ s, c i • prodV D (W := (Reg.pair a b hab).sig)
          (Function.update (Function.update ψ a (u i)) b (v i)) := by
    rw [prodV_sig_pair, regOp_pairGate_pairEnc, hG, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, prodV_sig_pair a b hab
      (Function.update (Function.update ψ a (u i)) b (v i))]
    congr 2
    simp [Function.update_of_ne hab]
  rw [hblock]
  have htenv : tenv D (∑ i ∈ s, c i • prodV D (W := (Reg.pair a b hab).sig)
        (Function.update (Function.update ψ a (u i)) b (v i)))
        (prodV D (W := (univ : Finset L) \ (Reg.pair a b hab).sig) ψ)
      = ∑ i ∈ s, c i • tenv D (prodV D (W := (Reg.pair a b hab).sig)
          (Function.update (Function.update ψ a (u i)) b (v i)))
          (prodV D (W := (univ : Finset L) \ (Reg.pair a b hab).sig) ψ) := by
    change tenvBil D (∑ i ∈ s, c i • _) _ = _
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply]
    rfl
  rw [htenv, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  congr 1
  rw [prodV_split D h (Function.update (Function.update ψ a (u i)) b (v i))]
  refine congrArg (castH D (union_sdiff_of_subset h)) (congrArg₂ (tenv D) rfl ?_)
  refine prodV_congr D fun l hl => ?_
  have hla : l ≠ a := fun hc =>
    (mem_sdiff.1 hl).2 (by rw [hc]; exact (Reg.pair a b hab).apply_mem_sig 0)
  have hlb : l ≠ b := fun hc =>
    (mem_sdiff.1 hl).2 (by rw [hc]; exact (Reg.pair a b hab).apply_mem_sig 1)
  rw [Function.update_of_ne hlb, Function.update_of_ne hla]

end PairSum

/-! ## §4. The sum world: classical-state helpers -/

section SumWorld

variable {L₁ L₂ : Type*}

theorem elim_update_inl [DecidableEq L₁] [DecidableEq L₂] (f : L₁ → Bool) (e : L₂ → Bool)
    (a : L₁) (b : Bool) :
    Function.update (Sum.elim f e) (Sum.inl a : L₁ ⊕ L₂) b
      = Sum.elim (Function.update f a b) e := by
  funext i
  cases i with
  | inl s =>
      by_cases hs : s = a
      · subst hs
        rw [Function.update_self]
        simp
      · rw [Function.update_of_ne (fun hc => hs (Sum.inl_injective hc))]
        simp [Function.update_of_ne hs]
  | inr t =>
      rw [Function.update_of_ne (fun hc => Sum.inl_ne_inr hc.symm)]
      simp

theorem elim_update_inr [DecidableEq L₁] [DecidableEq L₂] (f : L₁ → Bool) (e : L₂ → Bool)
    (c : L₂) (b : Bool) :
    Function.update (Sum.elim f e) (Sum.inr c : L₁ ⊕ L₂) b
      = Sum.elim f (Function.update e c b) := by
  funext i
  cases i with
  | inl s =>
      rw [Function.update_of_ne (fun hc => Sum.inl_ne_inr hc)]
      simp
  | inr t =>
      by_cases ht : t = c
      · subst ht
        rw [Function.update_self]
        simp
      · rw [Function.update_of_ne (fun hc => ht (Sum.inr_injective hc))]
        simp [Function.update_of_ne ht]

theorem elim_eq_elim_iff (f g : L₁ → Bool) (e e' : L₂ → Bool) :
    Sum.elim f e = Sum.elim g e' ↔ f = g ∧ e = e' := by
  constructor
  · intro h
    exact ⟨funext fun s => congrFun h (Sum.inl s), funext fun t => congrFun h (Sum.inr t)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end SumWorld

/-! ## §5. The ancilla-block embedding -/

section Embed

variable {L₁ L₂ : Type*} [Fintype L₁] [DecidableEq L₁] [Fintype L₂] [DecidableEq L₂]

/-- **The ancilla-block embedding**: the system block in the arbitrary state
`w`, the ancilla block in the computational basis state `e`. -/
noncomputable def ancEmbed (e : L₂ → Bool) :
    HS (QubitCells L₁) (univ : Finset L₁) →ₗ[ℂ]
      HS (QubitCells (L₁ ⊕ L₂)) (univ : Finset (L₁ ⊕ L₂)) where
  toFun w := WithLp.toLp 2 fun g =>
    if (fun a : L₂ => g ⟨Sum.inr a, mem_univ _⟩) = e
    then w (qbIdx L₁ fun s => g ⟨Sum.inl s, mem_univ _⟩) else 0
  map_add' w₁ w₂ := by
    refine PiLp.ext fun g => ?_
    by_cases hg : (fun a : L₂ => g ⟨Sum.inr a, mem_univ _⟩) = e <;>
      simp [hg]
  map_smul' cc w := by
    refine PiLp.ext fun g => ?_
    by_cases hg : (fun a : L₂ => g ⟨Sum.inr a, mem_univ _⟩) = e <;>
      simp [hg]

theorem ancEmbed_apply (e : L₂ → Bool) (w : HS (QubitCells L₁) (univ : Finset L₁))
    (g : QIdx (QubitCells (L₁ ⊕ L₂)) (univ : Finset (L₁ ⊕ L₂))) :
    ancEmbed e w g
      = if (fun a : L₂ => g ⟨Sum.inr a, mem_univ _⟩) = e
        then w (qbIdx L₁ fun s => g ⟨Sum.inl s, mem_univ _⟩) else 0 := rfl

/-- The embedding of a basis ket is the joint basis ket. -/
theorem ancEmbed_deltav (e : L₂ → Bool) (f : L₁ → Bool) :
    ancEmbed (L₁ := L₁) (L₂ := L₂) e (deltav (QubitCells L₁) (qbIdx L₁ f))
      = deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) (Sum.elim f e)) := by
  refine PiLp.ext fun g => ?_
  conv_rhs => rw [deltav_apply]
  rw [ancEmbed_apply]
  by_cases hR : (fun a : L₂ => g ⟨Sum.inr a, mem_univ _⟩) = e
  · rw [if_pos hR, deltav_apply]
    by_cases hL : (qbIdx L₁ fun s => g ⟨Sum.inl s, mem_univ _⟩) = qbIdx L₁ f
    · rw [if_pos hL, if_pos]
      funext i
      obtain ⟨i, hi⟩ := i
      cases i with
      | inl s => exact congrFun (qbIdx_injective hL) s
      | inr t => exact congrFun hR t
    · rw [if_neg hL, if_neg]
      intro hc
      subst hc
      exact hL (by funext s; rfl)
  · rw [if_neg hR, if_neg]
    intro hc
    subst hc
    exact hR (by funext a; rfl)

/-- **The expansion of an embedded state** over the joint basis. -/
theorem ancEmbed_expand (e : L₂ → Bool) (w : HS (QubitCells L₁) (univ : Finset L₁)) :
    ancEmbed (L₁ := L₁) (L₂ := L₂) e w
      = ∑ f : L₁ → Bool, w (qbIdx L₁ f) •
          deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) (Sum.elim f e)) := by
  have h := congrArg (ancEmbed (L₁ := L₁) (L₂ := L₂) e) (qubitHS_expand w)
  simp only [map_sum, map_smul, ancEmbed_deltav] at h
  exact h

/-- Embeddings at distinct ancilla patterns are orthogonal; at the same
pattern the embedding preserves the inner product. -/
theorem inner_ancEmbed (e e' : L₂ → Bool) (w w' : HS (QubitCells L₁) (univ : Finset L₁)) :
    (⟪ancEmbed (L₁ := L₁) (L₂ := L₂) e w, ancEmbed (L₁ := L₁) (L₂ := L₂) e' w'⟫ : ℂ)
      = if e = e' then (⟪w, w'⟫ : ℂ) else 0 := by
  rw [ancEmbed_expand, ancEmbed_expand, sum_inner]
  have hterm : ∀ f : L₁ → Bool,
      (⟪w (qbIdx L₁ f) • deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) (Sum.elim f e)),
        ∑ g : L₁ → Bool, w' (qbIdx L₁ g) •
          deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) (Sum.elim g e'))⟫ : ℂ)
      = (starRingEnd ℂ) (w (qbIdx L₁ f)) *
          ∑ g : L₁ → Bool, w' (qbIdx L₁ g) *
            (if f = g ∧ e = e' then 1 else 0) := by
    intro f
    simp only [inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hdd := dv_dot (D := QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) (Sum.elim f e))
      (qbIdx (L₁ ⊕ L₂) (Sum.elim g e'))
    rw [hdd]
    have hiff : (qbIdx (L₁ ⊕ L₂) (Sum.elim f e) = qbIdx (L₁ ⊕ L₂) (Sum.elim g e'))
        ↔ (f = g ∧ e = e') := by
      constructor
      · intro h
        exact (elim_eq_elim_iff f g e e').mp (qbIdx_injective h)
      · rintro ⟨rfl, rfl⟩
        rfl
    by_cases hc : f = g ∧ e = e'
    · rw [if_pos (hiff.mpr hc), if_pos hc]
      ring
    · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
      ring
  rw [Finset.sum_congr rfl fun f _ => hterm f]
  by_cases hee : e = e'
  · subst hee
    rw [if_pos rfl, inner_qubitHS_expand]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hsum : (∑ g : L₁ → Bool, w' (qbIdx L₁ g) * (if f = g ∧ e = e then 1 else 0))
        = w' (qbIdx L₁ f) := by
      rw [Finset.sum_eq_single f]
      · rw [if_pos ⟨rfl, rfl⟩, mul_one]
      · intro g _ hg
        rw [if_neg (fun h => hg h.1.symm), mul_zero]
      · intro hc
        exact absurd (mem_univ _) hc
    rw [hsum]
  · rw [if_neg hee]
    refine Finset.sum_eq_zero fun f _ => ?_
    have hsum : (∑ g : L₁ → Bool, w' (qbIdx L₁ g) * (if f = g ∧ e = e' then 1 else 0))
        = 0 := Finset.sum_eq_zero fun g _ => by
      rw [if_neg (fun h => hee h.2), mul_zero]
    rw [hsum, mul_zero]

/-- The embedding is an isometry. -/
theorem norm_ancEmbed (e : L₂ → Bool) (w : HS (QubitCells L₁) (univ : Finset L₁)) :
    ‖ancEmbed (L₁ := L₁) (L₂ := L₂) e w‖ = ‖w‖ := by
  have h := inner_ancEmbed (L₁ := L₁) (L₂ := L₂) e e w w
  rw [if_pos rfl, inner_self_eq_norm_sq_to_K (𝕜 := ℂ),
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at h
  have h2 : ‖ancEmbed (L₁ := L₁) (L₂ := L₂) e w‖ ^ 2 = ‖w‖ ^ 2 := by
    exact_mod_cast h
  calc ‖ancEmbed (L₁ := L₁) (L₂ := L₂) e w‖
      = Real.sqrt (‖ancEmbed (L₁ := L₁) (L₂ := L₂) e w‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖w‖ ^ 2) := by rw [h2]
    _ = ‖w‖ := Real.sqrt_sq (norm_nonneg _)

/-- `(ancEmbed e)† ∘ ancEmbed e' = δ_{e e'}`. -/
theorem adjoint_ancEmbed_comp (e e' : L₂ → Bool)
    (w : HS (QubitCells L₁) (univ : Finset L₁)) :
    LinearMap.adjoint (ancEmbed (L₁ := L₁) (L₂ := L₂) e)
        (ancEmbed (L₁ := L₁) (L₂ := L₂) e' w)
      = if e = e' then w else 0 := by
  refine ext_inner_left ℂ fun u => ?_
  rw [LinearMap.adjoint_inner_right, inner_ancEmbed]
  by_cases hee : e = e'
  · rw [if_pos hee, if_pos hee]
  · rw [if_neg hee, if_neg hee, inner_zero_right]

end Embed

/-! ## §6. Gate collapses on embedded states -/

section GateCollapse

variable {L₁ L₂ : Type*} [Fintype L₁] [DecidableEq L₁] [Fintype L₂] [DecidableEq L₂]

/-- A system gate commutes past the embedding. -/
theorem gateAt_inl_ancEmbed (a : L₁) (U : UnitaryOp 𝕢) (e : L₂ → Bool)
    (w : HS (QubitCells L₁) (univ : Finset L₁)) :
    gateAt (L₁ ⊕ L₂) (Sum.inl a) U (ancEmbed (L₁ := L₁) (L₂ := L₂) e w)
      = ancEmbed (L₁ := L₁) (L₂ := L₂) e (gateAt L₁ a U w) := by
  conv_lhs => rw [qubitHS_expand w]
  conv_rhs => rw [qubitHS_expand w]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun f _ => ?_
  refine congrArg (_ • ·) ?_
  rw [ancEmbed_deltav, gateAt_deltav_expand, gateAt_deltav_expand]
  simp only [map_sum, map_smul, ancEmbed_deltav]
  refine Finset.sum_congr rfl fun b _ => ?_
  have harg : Sum.elim f e (Sum.inl a) = f a := rfl
  rw [harg, elim_update_inl]

/-- A one-cell ancilla gate whose action on the stored basis bit is a scalar
times a basis ket collapses on the embedding. -/
theorem gateAt_inr_ancEmbed (c : L₂) (U : UnitaryOp 𝕢) (e : L₂ → Bool)
    {γ : ℂ} {b' : Bool}
    (hU : (U : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single (e c) 1)
      = γ • EuclideanSpace.single b' 1)
    (w : HS (QubitCells L₁) (univ : Finset L₁)) :
    gateAt (L₁ ⊕ L₂) (Sum.inr c) U (ancEmbed (L₁ := L₁) (L₂ := L₂) e w)
      = γ • ancEmbed (L₁ := L₁) (L₂ := L₂) (Function.update e c b') w := by
  rw [ancEmbed_expand e w, ancEmbed_expand (Function.update e c b') w]
  simp only [map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [gateAt_deltav (Sum.inr c) U (Sum.elim f e) (by exact hU),
    elim_update_inr, smul_comm]

/-- A two-cell ancilla gate with expanded basis action collapses on the
embedding: each output pattern updates the ancilla state. -/
theorem pairGate_anc_ancEmbed (c d : L₂) (hcd : (Sum.inr c : L₁ ⊕ L₂) ≠ Sum.inr d)
    (G : UnitaryOp (EuclideanSpace ℂ (Bool × Bool)))
    (e : L₂ → Bool) {ι : Type*} (s : Finset ι) (coef : ι → ℂ) (p : ι → Bool × Bool)
    (hG : (G : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair (qbit (e c)) (qbit (e d)))
      = ∑ i ∈ s, coef i • vpair (qbit (p i).1) (qbit (p i).2))
    (w : HS (QubitCells L₁) (univ : Finset L₁)) :
    regLift (Reg.pair (Sum.inr c : L₁ ⊕ L₂) (Sum.inr d) hcd)
      (pairGate (D := QubitCells (L₁ ⊕ L₂)) (Sum.inr c) (Sum.inr d) hcd G)
      (ancEmbed (L₁ := L₁) (L₂ := L₂) e w)
      = ∑ i ∈ s, coef i • ancEmbed (L₁ := L₁) (L₂ := L₂)
          (Function.update (Function.update e c (p i).1) d (p i).2) w := by
  have key : ∀ f : L₁ → Bool,
      regLift (Reg.pair (Sum.inr c : L₁ ⊕ L₂) (Sum.inr d) hcd)
        (pairGate (D := QubitCells (L₁ ⊕ L₂)) (Sum.inr c) (Sum.inr d) hcd G)
        (deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) (Sum.elim f e)))
      = ∑ i ∈ s, coef i • deltav (QubitCells (L₁ ⊕ L₂))
          (qbIdx (L₁ ⊕ L₂)
            (Sum.elim f (Function.update (Function.update e c (p i).1) d (p i).2))) := by
    intro f
    have h1 : deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) (Sum.elim f e))
        = prodV (QubitCells (L₁ ⊕ L₂)) (W := univ)
            (fun i => EuclideanSpace.single (Sum.elim f e i) 1) :=
      (prodV_single (QubitCells (L₁ ⊕ L₂)) (Sum.elim f e)).symm
    have hG' : (G : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] EuclideanSpace ℂ (Bool × Bool))
        (vpair ((fun i : L₁ ⊕ L₂ => (EuclideanSpace.single (Sum.elim f e i) 1 :
            EuclideanSpace ℂ (QubitCells (L₁ ⊕ L₂) i))) (Sum.inr c))
          ((fun i : L₁ ⊕ L₂ => (EuclideanSpace.single (Sum.elim f e i) 1 :
            EuclideanSpace ℂ (QubitCells (L₁ ⊕ L₂) i))) (Sum.inr d)))
        = ∑ i ∈ s, coef i • vpair (EuclideanSpace.single (p i).1 1)
            (EuclideanSpace.single (p i).2 1) := hG
    rw [h1, regLift_pairGate_prodV_sum s (Sum.inr c) (Sum.inr d) hcd G coef
      (fun i => EuclideanSpace.single (p i).1 1) (fun i => EuclideanSpace.single (p i).2 1)
      (fun i => EuclideanSpace.single (Sum.elim f e i) 1) hG']
    refine Finset.sum_congr rfl fun i _ => ?_
    refine congrArg (_ • ·) ?_
    have h2 : Function.update (Function.update
          (fun l : L₁ ⊕ L₂ => (EuclideanSpace.single (Sum.elim f e l) 1 :
            EuclideanSpace ℂ (QubitCells (L₁ ⊕ L₂) l)))
          (Sum.inr c) (EuclideanSpace.single (p i).1 1)) (Sum.inr d)
          (EuclideanSpace.single (p i).2 1)
        = fun l : L₁ ⊕ L₂ => EuclideanSpace.single
            (Sum.elim f (Function.update (Function.update e c (p i).1) d (p i).2) l) 1 := by
      funext l
      rcases eq_or_ne l (Sum.inr d : L₁ ⊕ L₂) with rfl | hld
      · rw [Function.update_self,
          show Sum.elim f (Function.update (Function.update e c (p i).1) d (p i).2)
            (Sum.inr d : L₁ ⊕ L₂) = (p i).2 from by simp]
      · rw [Function.update_of_ne hld]
        rcases eq_or_ne l (Sum.inr c : L₁ ⊕ L₂) with rfl | hlc
        · rw [Function.update_self,
            show Sum.elim f (Function.update (Function.update e c (p i).1) d (p i).2)
              (Sum.inr c : L₁ ⊕ L₂) = (p i).1 from by
              have hcd' : c ≠ d := fun hc => hcd (by rw [hc])
              simp [Function.update_of_ne hcd']]
        · rw [Function.update_of_ne hlc]
          congr 1
          cases l with
          | inl s' => rfl
          | inr t =>
              have htd : t ≠ d := fun hc => hld (by rw [hc])
              have htc : t ≠ c := fun hc => hlc (by rw [hc])
              show Sum.elim f e (Sum.inr t) = _
              simp [Function.update_of_ne htd, Function.update_of_ne htc]
    rw [h2, prodV_single]
    rfl
  rw [ancEmbed_expand e w, map_sum]
  rw [show (∑ i ∈ s, coef i • ancEmbed (L₁ := L₁) (L₂ := L₂)
        (Function.update (Function.update e c (p i).1) d (p i).2) w)
      = ∑ i ∈ s, ∑ f : L₁ → Bool, coef i • (w (qbIdx L₁ f) •
          deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂)
            (Sum.elim f (Function.update (Function.update e c (p i).1) d (p i).2)))) from
    Finset.sum_congr rfl fun i _ => by rw [ancEmbed_expand, Finset.smul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [map_smul, key f, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

/-- **The controlled-gate collapse**: a controlled gate with ancilla control
`c` and system target `a` fires exactly when the stored control bit is set. -/
theorem pairGate_ctrl_ancEmbed (c : L₂) (a : L₁) (V : UnitaryOp 𝕢) (e : L₂ → Bool)
    (w : HS (QubitCells L₁) (univ : Finset L₁)) :
    regLift (Reg.pair (Sum.inr c : L₁ ⊕ L₂) (Sum.inl a) Sum.inr_ne_inl)
      (pairGate (D := QubitCells (L₁ ⊕ L₂)) (Sum.inr c) (Sum.inl a) Sum.inr_ne_inl (control V))
      (ancEmbed (L₁ := L₁) (L₂ := L₂) e w)
      = if e c then ancEmbed (L₁ := L₁) (L₂ := L₂) e (gateAt L₁ a V w)
        else ancEmbed (L₁ := L₁) (L₂ := L₂) e w := by
  have key : ∀ f : L₁ → Bool,
      regLift (Reg.pair (Sum.inr c : L₁ ⊕ L₂) (Sum.inl a) Sum.inr_ne_inl)
        (pairGate (D := QubitCells (L₁ ⊕ L₂)) (Sum.inr c) (Sum.inl a) Sum.inr_ne_inl (control V))
        (deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) (Sum.elim f e)))
      = if e c
        then gateAt (L₁ ⊕ L₂) (Sum.inl a) V
          (deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) (Sum.elim f e)))
        else deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) (Sum.elim f e)) := by
    intro f
    have h1 : deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) (Sum.elim f e))
        = prodV (QubitCells (L₁ ⊕ L₂)) (W := univ)
            (fun i => EuclideanSpace.single (Sum.elim f e i) 1) :=
      (prodV_single (QubitCells (L₁ ⊕ L₂)) (Sum.elim f e)).symm
    rw [h1]
    set ψ : ∀ i : L₁ ⊕ L₂, EuclideanSpace ℂ (QubitCells (L₁ ⊕ L₂) i) :=
      fun i => EuclideanSpace.single (Sum.elim f e i) 1 with hψdef
    cases hec : e c
    · have hG : (control V : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] _)
          (vpair (ψ (Sum.inr c)) (ψ (Sum.inl a)))
          = vpair (ψ (Sum.inr c)) (ψ (Sum.inl a)) := by
        have hc0 : ψ (Sum.inr c) = q0 := by
          rw [hψdef]
          show EuclideanSpace.single (e c) 1 = q0
          rw [hec]
          rfl
        rw [hc0]
        exact control_vpair_q0 V _
      rw [regLift_pairGate_prodV _ _ _ (control V) ψ hG,
        Function.update_eq_self, Function.update_eq_self]
      simp
    · have hG : (control V : EuclideanSpace ℂ (Bool × Bool) →ₗ[ℂ] _)
          (vpair (ψ (Sum.inr c)) (ψ (Sum.inl a)))
          = vpair (ψ (Sum.inr c)) ((V : 𝕢 →ₗ[ℂ] 𝕢) (ψ (Sum.inl a))) := by
        have hc1 : ψ (Sum.inr c) = q1 := by
          rw [hψdef]
          show EuclideanSpace.single (e c) 1 = q1
          rw [hec]
          rfl
        rw [hc1]
        exact control_vpair_q1 V _
      rw [regLift_pairGate_prodV _ _ _ (control V) ψ hG,
        Function.update_eq_self, ← gateAt_prodV]
      simp
  by_cases hec : e c
  · rw [if_pos hec, ← gateAt_inl_ancEmbed]
    rw [ancEmbed_expand, map_sum, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_smul, map_smul, key f, if_pos hec]
  · rw [if_neg hec]
    conv_rhs => rw [ancEmbed_expand]
    rw [ancEmbed_expand, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_smul, key f, if_neg (by simpa using hec)]

end GateCollapse

/-! ## §7. Store-parameterized pure-state families -/

section StateFam

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-- The assertion "the world is in the state `v σ`" — a store-indexed family
of pure-state projectors (the store-parameterized `Assn.ofState`). -/
noncomputable def Assn.ofStateFam (v : σT → HS D (univ : Finset L))
    (hv : ∀ σ, ‖v σ‖ = 1) : Assn σT D :=
  ⟨fun σ => outerLM (v σ) (v σ), fun σ => isEffect_outerLM_self (hv σ)⟩

@[simp]
theorem Assn.ofStateFam_op (v : σT → HS D (univ : Finset L)) (hv : ∀ σ, ‖v σ‖ = 1)
    (σ : σT) : (Assn.ofStateFam (σT := σT) v hv).op σ = outerLM (v σ) (v σ) := rfl

/-- **(Ax-Uni) at a store-indexed family of pure states, with a
store-computed gate** — the parameterized-gate form of
`DerivTot.unitary_state`:

```
⊢ₜ {|v σ⟩⟨v σ|}  q̄ *= U(σ)  {|w σ⟩⟨w σ|}    given  ∀ σ, regLift r (U σ) (v σ) = w σ.
```

Built from the `DerivTot` constructors `.unitary` (Ax-Uni) and `.conseq`
(R-Conseq) alone. -/
theorem DerivTot.unitary_stateFam {k : ℕ} (r : Reg L k)
    (U : σT → UnitaryOp (TSpace D r.toFun))
    {v w : σT → HS D (univ : Finset L)} (hv : ∀ σ, ‖v σ‖ = 1) (hw : ∀ σ, ‖w σ‖ = 1)
    (hU : ∀ σ, regLift r ((U σ : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)) (v σ) = w σ) :
    DerivTot (σT := σT) (Assn.ofStateFam v hv)
      (.unitary k (RegExpr.const r) U)
      (Assn.ofStateFam w hw) := by
  refine DerivTot.conseq ?_ (DerivTot.unitary (RegExpr.const r) U _) (Assn.le_refl' _)
  intro σ
  refine le_of_eq (Eq.symm (Eq.trans
    (Assn.unitaryPre_op_of_dist _ _ _ (σ := σ) r.inj) ?_))
  rw [Assn.ofStateFam_op]
  exact adjoint_conj_outerLM_state r (U σ) (hU σ)

end StateFam

/-! ## §8. Straight-line chains of store-computed unitary gates -/

section Chain

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-- `regLift` is multiplicative at a fixed register. -/
theorem regLift_comp {k : ℕ} (r : Reg L k)
    (A B : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) :
    regLift r A ∘ₗ regLift r B = regLift r (A ∘ₗ B) := by
  rw [regLift, regLift, regLift, Reg.op_comp, liftF_comp]

/-- `regLift` of the identity is the identity. -/
theorem regLift_one {k : ℕ} (r : Reg L k) :
    regLift (D := D) r (1 : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) = 1 := by
  rw [regLift, Reg.op_one, liftF_one]

/-- Transported unitaries compose (coercion form). -/
theorem congr_coe_comp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (e : E ≃ₗᵢ[ℂ] F) (U U' : UnitaryOp E) :
    (UnitaryOp.congr e U : F →ₗ[ℂ] F) ∘ₗ (UnitaryOp.congr e U' : F →ₗ[ℂ] F)
      = (UnitaryOp.congr e (U * U') : F →ₗ[ℂ] F) := by
  refine LinearMap.ext fun t => ?_
  rw [LinearMap.comp_apply, UnitaryOp.congr_apply, UnitaryOp.congr_apply,
    UnitaryOp.congr_apply, LinearIsometryEquiv.symm_apply_apply, UnitaryOp.coe_mul,
    LinearMap.comp_apply]

/-- The transport of the identity is the identity. -/
theorem congr_coe_one {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (e : E ≃ₗᵢ[ℂ] F) :
    (UnitaryOp.congr e (1 : UnitaryOp E) : F →ₗ[ℂ] F) = 1 := by
  refine LinearMap.ext fun t => ?_
  rw [UnitaryOp.congr_apply, UnitaryOp.coe_one, Module.End.one_apply,
    LinearIsometryEquiv.apply_symm_apply, Module.End.one_apply]

/-- `singleGate` composes (coercion form). -/
theorem singleGate_coe_comp (a : L) (U V : UnitaryOp (EuclideanSpace ℂ (D a))) :
    ((singleGate D a U : UnitaryOp (TSpace D (Reg.single a).toFun)) :
      TSpace D (Reg.single a).toFun →ₗ[ℂ] TSpace D (Reg.single a).toFun)
      ∘ₗ ((singleGate D a V : UnitaryOp (TSpace D (Reg.single a).toFun)) :
        TSpace D (Reg.single a).toFun →ₗ[ℂ] TSpace D (Reg.single a).toFun)
      = ((singleGate D a (U * V) : UnitaryOp (TSpace D (Reg.single a).toFun)) :
        TSpace D (Reg.single a).toFun →ₗ[ℂ] TSpace D (Reg.single a).toFun) := by
  unfold singleGate euclCongrOp
  exact congr_coe_comp _ U V

/-- `singleGate` of the identity is the identity (coercion form). -/
theorem singleGate_coe_one (a : L) :
    ((singleGate D a (1 : UnitaryOp (EuclideanSpace ℂ (D a))) :
      UnitaryOp (TSpace D (Reg.single a).toFun)) :
      TSpace D (Reg.single a).toFun →ₗ[ℂ] TSpace D (Reg.single a).toFun) = 1 := by
  unfold singleGate euclCongrOp
  exact congr_coe_one _

/-- `pairGate` composes (coercion form). -/
theorem pairGate_coe_comp (a b : L) (hab : a ≠ b)
    (U V : UnitaryOp (EuclideanSpace ℂ (D a × D b))) :
    ((pairGate a b hab U : UnitaryOp (TSpace D (Reg.pair a b hab).toFun)) :
      TSpace D (Reg.pair a b hab).toFun →ₗ[ℂ] TSpace D (Reg.pair a b hab).toFun)
      ∘ₗ ((pairGate a b hab V : UnitaryOp (TSpace D (Reg.pair a b hab).toFun)) :
        TSpace D (Reg.pair a b hab).toFun →ₗ[ℂ] TSpace D (Reg.pair a b hab).toFun)
      = ((pairGate a b hab (U * V) : UnitaryOp (TSpace D (Reg.pair a b hab).toFun)) :
        TSpace D (Reg.pair a b hab).toFun →ₗ[ℂ] TSpace D (Reg.pair a b hab).toFun) := by
  refine LinearMap.ext fun t => ?_
  obtain ⟨w, rfl⟩ := (pairIso D a b hab).surjective t
  rw [LinearMap.comp_apply, pairGate_apply_pairIso, pairGate_apply_pairIso,
    pairGate_apply_pairIso, UnitaryOp.coe_mul, LinearMap.comp_apply]

/-- `pairGate` of the identity is the identity (coercion form). -/
theorem pairGate_coe_one (a b : L) (hab : a ≠ b) :
    ((pairGate a b hab (1 : UnitaryOp (EuclideanSpace ℂ (D a × D b))) :
      UnitaryOp (TSpace D (Reg.pair a b hab).toFun)) :
      TSpace D (Reg.pair a b hab).toFun →ₗ[ℂ] TSpace D (Reg.pair a b hab).toFun) = 1 := by
  refine LinearMap.ext fun t => ?_
  obtain ⟨w, rfl⟩ := (pairIso D a b hab).surjective t
  rw [pairGate_apply_pairIso, UnitaryOp.coe_one, Module.End.one_apply,
    Module.End.one_apply]

/-- The adjoint of a unitary is the operator that undoes it. -/
theorem adjoint_eq_of_comp_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {K F : E →ₗ[ℂ] E}
    (hK : IsUnitary K) (h : F ∘ₗ K = 1) : LinearMap.adjoint K = F := by
  have h2 : K ∘ₗ LinearMap.adjoint K = 1 := hK.2
  calc LinearMap.adjoint K
      = 1 ∘ₗ LinearMap.adjoint K := by
        rw [Module.End.one_eq_id, LinearMap.id_comp]
    _ = (F ∘ₗ K) ∘ₗ LinearMap.adjoint K := by rw [h]
    _ = F ∘ₗ (K ∘ₗ LinearMap.adjoint K) := by rw [LinearMap.comp_assoc]
    _ = F := by rw [h2, Module.End.one_eq_id, LinearMap.comp_id]

/-- `chainOp` splits over list append (the head of the list acts first). -/
theorem chainOp_append {ι : Type*} (l₁ l₂ : List ι) (K : ι → EndM D (univ : Finset L)) :
    chainOp (l₁ ++ l₂) K = chainOp l₂ K ∘ₗ chainOp l₁ K := by
  induction l₁ with
  | nil =>
      rw [List.nil_append, chainOp_nil, Module.End.one_eq_id, LinearMap.comp_id]
  | cons i t ih =>
      rw [List.cons_append, chainOp_cons, chainOp_cons, ih, LinearMap.comp_assoc]

/-- The adjoint of a gate chain is the reversed chain of the adjoints. -/
theorem adjoint_chainOp {ι : Type*} (l : List ι) (K : ι → EndM D (univ : Finset L)) :
    LinearMap.adjoint (chainOp l K)
      = chainOp l.reverse (fun i => LinearMap.adjoint (K i)) := by
  induction l with
  | nil =>
      rw [chainOp_nil, List.reverse_nil, chainOp_nil, LinearMap.adjoint_one]
  | cons i t ih =>
      rw [chainOp_cons, LinearMap.adjoint_comp, ih, List.reverse_cons, chainOp_append,
        chainOp_cons, chainOp_nil, Module.End.one_eq_id, LinearMap.id_comp]

/-- **A `for`-fold of store-computed unitary gates on a pure-state family**:
the postcondition is the family evolved by the semantic chain operator.  One
(Ax-Uni) + (R-Conseq) per gate, glued by (R-Seq) and closed by (Ax-Ski) — the
straight-line special case of the invariant-chain rule. -/
theorem DerivTot.forProg_unitary_chain {ι : Type*} (l : List ι) (k : ι → ℕ)
    (r : ∀ i, Reg L (k i)) (U : ∀ i, σT → UnitaryOp (TSpace D (r i).toFun))
    (v : σT → HS D (univ : Finset L)) (hv : ∀ σ, ‖v σ‖ = 1) :
    DerivTot (σT := σT) (Assn.ofStateFam v hv)
      (Qhl.forProg l fun i => Prog.unitary (k i) (RegExpr.const (r i)) (U i))
      (Assn.ofStateFam
        (fun σ => chainOp l
          (fun i => regLift (r i) ((U i σ : TSpace D (r i).toFun →ₗ[ℂ] TSpace D (r i).toFun)))
          (v σ))
        (fun σ => norm_eq_one_of_isUnitary
          (isUnitary_chainOp l _ fun i => isUnitary_regLift _ _) (hv σ))) := by
  induction l generalizing v with
  | nil => exact DerivTot.skip _
  | cons i t ih =>
      exact DerivTot.seq
        (DerivTot.unitary_stateFam (r i) (U i) hv
          (fun σ => norm_eq_one_of_isUnitary (isUnitary_regLift _ _) (hv σ))
          (fun σ => rfl))
        (ih (fun σ => regLift (r i)
            ((U i σ : TSpace D (r i).toFun →ₗ[ℂ] TSpace D (r i).toFun)) (v σ))
          (fun σ => norm_eq_one_of_isUnitary (isUnitary_regLift _ _) (hv σ)))

end Chain

end Qhl
