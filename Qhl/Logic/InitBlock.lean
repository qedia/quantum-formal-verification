import Qhl.Logic.PreCompute
import Qhl.Logic.AncillaEmbed
import Qhl.Logic.Rules

/-!
# The initialisation transformer on an ancilla block, as a system-operator lift

The internalization layer for success-probability triples.  A triple whose
precondition is an *effect* (not a pure-state projector) is derived backward:
(Ax-Uni) + (R-Seq) fold the postcondition through the gates, and (Ax-Init)
then pushes the folded effect through the initialisation channel of the
ancilla block.  This file supplies the generic pieces of that computation, on
a **sum world** `L₁ ⊕ L₂` of qubit cells (`L₁` the system block, `L₂` the
ancilla block):

* §1 — the `wp`-fold *rules*: `DerivTot.forProg_foldr` (a `for` fold is
  derivable from any per-iteration backward transformer) and its unitary-leaf
  instance `DerivTot.forProg_unitaryPre`; the const-register displays
  `Assn.unitaryPre_const_op` / `foldr_unitaryPre_const_op` and the abstract
  fold display `foldr_op_conj`.
* §2 — Löwner-order helpers: `real_smul_le_real_smul` and the rectangular
  rank-one conjugation `adjoint_comp_outerLM_self_comp`.
* §3 — `Assn.scaled`: an effect family scaled by `t ∈ [0,1]` is an effect
  family (the shape a success-probability precondition takes).
* §4 — the system-operator lift `sysLift M = 1_a ⊗ M`: the sum, over all
  ancilla basis patterns, of `ancEmbed e ∘ₗ M ∘ₗ (ancEmbed e)†`; it preserves
  effects, the order, and scalars, and collapses on embedded states.
* §5 — **the (Ax-Init) display**: on the ancilla cell set the initialisation
  transformer *is* the system-operator lift of the vacuum block,
  `E†(A) = 1_a ⊗ (⟨0…0∣_a A ∣0…0⟩_a)` (`initPre_ancCells_op`), obtained from
  the Kraus display `Assn.initPre_op_eq_sum` by identifying each Kraus
  operator with `∣0…0⟩⟨e∣_a ⊗ 1 = ancEmbed 0 ∘ₗ (ancEmbed e)†`.

Everything is generic in the two label types, the cell family, the classical
store and the assertion: no program, no gate and no example fixture appears
(ownership test).
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace ComplexOrder

/-! ## §1. The `wp`-fold rules and displays -/

section Fold

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-- A `for` fold is derivable from any per-iteration backward transformer:
if `{T i B} C i {B}` is derivable for every index and every postcondition,
then the fold of `T` over the index list is a derivable precondition of the
`for` loop.  Pure (R-Seq) + (Ax-Ski) glue; the induction lives here. -/
theorem DerivTot.forProg_foldr {ι : Type*} (l : List ι) (C : ι → Prog σT D)
    (T : ι → Assn σT D → Assn σT D)
    (h : ∀ i (B : Assn σT D), DerivTot (T i B) (C i) B) (B : Assn σT D) :
    DerivTot (l.foldr T B) (Qhl.forProg l C) B := by
  induction l with
  | nil => exact DerivTot.skip B
  | cons i t ih => exact DerivTot.seq (h i (t.foldr T B)) ih

/-- The unitary-leaf instance of `DerivTot.forProg_foldr`: a `for` fold of
unitary steps at constant registers, with the folded (Ax-Uni) transformer as
precondition. -/
theorem DerivTot.forProg_unitaryPre {ι : Type*} (l : List ι) (k : ι → ℕ)
    (r : ∀ i, Reg L (k i)) (U : ∀ i (_ : σT), UnitaryOp (TSpace D (r i).toFun))
    (B : Assn σT D) :
    DerivTot
      (l.foldr (fun i A => A.unitaryPre (RegExpr.const (r i)) (U i)) B)
      (Qhl.forProg l fun i => Prog.unitary (k i) (RegExpr.const (r i)) (U i)) B :=
  DerivTot.forProg_foldr l _ _ (fun i B => DerivTot.unitary (RegExpr.const (r i)) (U i) B) B

/-- The (Ax-Uni) transformer at a constant register, displayed as a
conjugation by the lifted gate (the `Dist` side condition is discharged by
the register's own injectivity). -/
theorem Assn.unitaryPre_const_op (A : Assn σT D) {k : ℕ} (r : Reg L k)
    (U : ∀ _ : σT, UnitaryOp (TSpace D r.toFun)) (σ : σT) :
    (A.unitaryPre (RegExpr.const r) U).op σ
      = LinearMap.adjoint (regLift r (U σ)) ∘ₗ A.op σ ∘ₗ regLift r (U σ) :=
  A.unitaryPre_op_of_dist (RegExpr.const r) U (σ := σ) r.inj

/-- The folded (Ax-Uni) transformer at constant registers, displayed as one
conjugation by the semantic chain operator. -/
theorem foldr_unitaryPre_const_op {ι : Type*} (l : List ι) (k : ι → ℕ)
    (r : ∀ i, Reg L (k i)) (U : ∀ i (_ : σT), UnitaryOp (TSpace D (r i).toFun))
    (B : Assn σT D) (σ : σT) :
    (l.foldr (fun i A => A.unitaryPre (RegExpr.const (r i)) (U i)) B).op σ
      = LinearMap.adjoint (chainOp l fun i => regLift (r i) (U i σ)) ∘ₗ
          B.op σ ∘ₗ chainOp l fun i => regLift (r i) (U i σ) :=
  foldr_unitaryPre_op l k (fun i => RegExpr.const (r i)) U B σ (fun i => (r i).inj)

/-- The abstract fold display: any per-index transformer that acts at `σ` as
a conjugation folds to a single conjugation by the chain operator
(generalizes `foldr_unitaryPre_op` to compound iteration bodies). -/
theorem foldr_op_conj {ι : Type*} (l : List ι) (T : ι → Assn σT D → Assn σT D)
    (G : ι → EndM D (univ : Finset L)) (σ : σT)
    (hT : ∀ i (A : Assn σT D), (T i A).op σ
      = LinearMap.adjoint (G i) ∘ₗ A.op σ ∘ₗ G i) (B : Assn σT D) :
    (l.foldr T B).op σ
      = LinearMap.adjoint (chainOp l G) ∘ₗ B.op σ ∘ₗ chainOp l G := by
  induction l with
  | nil =>
      rw [List.foldr_nil, chainOp_nil, LinearMap.adjoint_one, Module.End.one_eq_id,
        LinearMap.id_comp, LinearMap.comp_id]
  | cons i t ih =>
      rw [List.foldr_cons, hT i, ih, chainOp_cons, LinearMap.adjoint_comp]
      simp only [LinearMap.comp_assoc]

end Fold

/-! ## §2. Löwner-order helpers -/

section Order

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Real scalings of a positive operator are Löwner-monotone in the scalar. -/
theorem real_smul_le_real_smul {a b : ℝ} (hab : a ≤ b) {X : E →ₗ[ℂ] E}
    (hX : X.IsPositive) : ((a : ℝ) : ℂ) • X ≤ ((b : ℝ) : ℂ) • X := by
  rw [le_iff_inner_le]
  intro w
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_right, inner_smul_right]
  have hz : 0 ≤ (⟪w, X w⟫ : ℂ) := (isPositive_iff_inner_nonneg X).mp hX w
  rw [Complex.le_def] at hz ⊢
  simp only [Complex.zero_re, Complex.zero_im] at hz
  refine ⟨?_, ?_⟩
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_right hab hz.1
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      ← hz.2]
    ring

/-- Splitting a conjugation by a composite: `(W ∘ P)† B (W ∘ P) = P† (W† B W) P`
(stated once generically so concrete uses never renormalize associativity). -/
theorem adjoint_comp_conj [FiniteDimensional ℂ E] (P W B : E →ₗ[ℂ] E) :
    LinearMap.adjoint (W ∘ₗ P) ∘ₗ B ∘ₗ W ∘ₗ P
      = LinearMap.adjoint P ∘ₗ (LinearMap.adjoint W ∘ₗ B ∘ₗ W) ∘ₗ P := by
  rw [LinearMap.adjoint_comp]
  simp only [LinearMap.comp_assoc]

/-- The rectangular rank-one conjugation: `K† ∘ ∣a⟩⟨a∣ ∘ K = ∣K†a⟩⟨K†a∣`. -/
theorem adjoint_comp_outerLM_self_comp [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (K : E →ₗ[ℂ] F) (a : F) :
    LinearMap.adjoint K ∘ₗ outerLM a a ∘ₗ K
      = outerLM (LinearMap.adjoint K a) (LinearMap.adjoint K a) := by
  refine LinearMap.ext fun u => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, outerLM_apply, outerLM_apply,
    map_smul, LinearMap.adjoint_inner_left]

end Order

/-! ## §3. Scaled effect families -/

section Scaled

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {σT : Type*}

/-- An effect family scaled by a real `t ∈ [0,1]` is an effect family — the
shape a success-probability precondition takes. -/
noncomputable def Assn.scaled (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (A : Assn σT D) :
    Assn σT D where
  op σ := ((t : ℝ) : ℂ) • A.op σ
  isEffect σ := by
    constructor
    · have h := real_smul_le_real_smul h0 (A.isEffect σ).isPositive
      rwa [Complex.ofReal_zero, zero_smul] at h
    · have h := real_smul_le_real_smul h1 (A.isEffect σ).isPositive
      rw [Complex.ofReal_one, one_smul] at h
      exact h.trans (A.isEffect σ).2

@[simp]
theorem Assn.scaled_op (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (A : Assn σT D) (σ : σT) :
    (A.scaled t h0 h1).op σ = ((t : ℝ) : ℂ) • A.op σ := rfl

end Scaled

/-! ## §4. The system-operator lift `1_a ⊗ M` on a qubit sum world -/

section SysLift

variable {L₁ L₂ : Type*} [Fintype L₁] [DecidableEq L₁] [Fintype L₂] [DecidableEq L₂]

/-- A total basis ket of the sum world is an embedded system basis ket at the
ancilla pattern it stores. -/
theorem deltav_eq_ancEmbed (g : L₁ ⊕ L₂ → Bool) :
    deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) g)
      = ancEmbed (L₁ := L₁) (L₂ := L₂) (fun a => g (Sum.inr a))
          (deltav (QubitCells L₁) (qbIdx L₁ fun s => g (Sum.inl s))) := by
  have h : Sum.elim (fun s => g (Sum.inl s)) (fun a => g (Sum.inr a)) = g :=
    funext fun i => by cases i <;> rfl
  rw [ancEmbed_deltav, h]

/-- **Completeness of the ancilla-pattern decomposition**: the embeddings at
all basis patterns resolve the identity of the sum world. -/
theorem sum_ancEmbed_comp_adjoint :
    (∑ e : L₂ → Bool, ancEmbed (L₁ := L₁) (L₂ := L₂) e ∘ₗ
        LinearMap.adjoint (ancEmbed (L₁ := L₁) (L₂ := L₂) e)) = 1 := by
  refine LinearMap.ext fun w => ?_
  rw [Module.End.one_apply, LinearMap.sum_apply]
  have key : ∀ e : L₂ → Bool,
      (ancEmbed (L₁ := L₁) (L₂ := L₂) e ∘ₗ
        LinearMap.adjoint (ancEmbed (L₁ := L₁) (L₂ := L₂) e)) w
      = ∑ g : L₁ ⊕ L₂ → Bool,
          (if (fun a => g (Sum.inr a)) = e
            then w (qbIdx (L₁ ⊕ L₂) g) • deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) g)
            else 0) := by
    intro e
    rw [LinearMap.comp_apply]
    conv_lhs => rw [qubitHS_expand (L := L₁ ⊕ L₂) w]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, map_smul, deltav_eq_ancEmbed g, adjoint_ancEmbed_comp]
    by_cases h : (fun a => g (Sum.inr a)) = e
    · rw [if_pos h.symm, if_pos h, ← h, ← deltav_eq_ancEmbed g]
    · rw [if_neg (fun hc => h hc.symm), if_neg h, map_zero, smul_zero]
  rw [Finset.sum_congr rfl fun e _ => key e, Finset.sum_comm]
  conv_rhs => rw [qubitHS_expand (L := L₁ ⊕ L₂) w]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_ite_eq univ (fun a => g (Sum.inr a))
    (fun _ => w (qbIdx (L₁ ⊕ L₂) g) • deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) g)),
    if_pos (mem_univ _)]

/-- **The system-operator lift** `1_a ⊗ M`: the operator that acts as `M` on
the system block and as the identity on the ancilla block, written as the sum
over ancilla basis patterns of the conjugated embeddings. -/
noncomputable def sysLift (M : EndM (QubitCells L₁) (univ : Finset L₁)) :
    EndM (QubitCells (L₁ ⊕ L₂)) (univ : Finset (L₁ ⊕ L₂)) :=
  ∑ e : L₂ → Bool, ancEmbed (L₁ := L₁) (L₂ := L₂) e ∘ₗ M ∘ₗ
    LinearMap.adjoint (ancEmbed (L₁ := L₁) (L₂ := L₂) e)

theorem sysLift_apply (M : EndM (QubitCells L₁) (univ : Finset L₁))
    (w : HS (QubitCells (L₁ ⊕ L₂)) (univ : Finset (L₁ ⊕ L₂))) :
    sysLift (L₂ := L₂) M w
      = ∑ e : L₂ → Bool, ancEmbed (L₁ := L₁) (L₂ := L₂) e
          (M (LinearMap.adjoint (ancEmbed (L₁ := L₁) (L₂ := L₂) e) w)) := by
  simp only [sysLift, LinearMap.sum_apply, LinearMap.comp_apply]

/-- The quadratic form of the lift is the sum of the block quadratic forms. -/
theorem inner_sysLift (M : EndM (QubitCells L₁) (univ : Finset L₁))
    (u w : HS (QubitCells (L₁ ⊕ L₂)) (univ : Finset (L₁ ⊕ L₂))) :
    (⟪u, sysLift (L₂ := L₂) M w⟫ : ℂ)
      = ∑ e : L₂ → Bool,
          (⟪LinearMap.adjoint (ancEmbed (L₁ := L₁) (L₂ := L₂) e) u,
            M (LinearMap.adjoint (ancEmbed (L₁ := L₁) (L₂ := L₂) e) w)⟫ : ℂ) := by
  rw [sysLift_apply, inner_sum]
  exact Finset.sum_congr rfl fun e _ => (LinearMap.adjoint_inner_left _ _ _).symm

theorem isPositive_sysLift {M : EndM (QubitCells L₁) (univ : Finset L₁)}
    (hM : M.IsPositive) : (sysLift (L₂ := L₂) M).IsPositive := by
  rw [isPositive_iff_inner_nonneg]
  intro w
  rw [inner_sysLift]
  exact Finset.sum_nonneg fun e _ => (isPositive_iff_inner_nonneg M).mp hM _

theorem sysLift_mono {M M' : EndM (QubitCells L₁) (univ : Finset L₁)}
    (h : M ≤ M') : sysLift (L₂ := L₂) M ≤ sysLift (L₂ := L₂) M' := by
  rw [le_iff_inner_le]
  intro w
  rw [inner_sysLift, inner_sysLift]
  exact Finset.sum_le_sum fun e _ => (le_iff_inner_le M M').mp h _

theorem sysLift_one :
    sysLift (L₁ := L₁) (L₂ := L₂) (1 : EndM (QubitCells L₁) (univ : Finset L₁)) = 1 := by
  rw [sysLift, ← sum_ancEmbed_comp_adjoint (L₁ := L₁) (L₂ := L₂)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Module.End.one_eq_id, LinearMap.id_comp]

/-- The lift preserves effects: `0 ≤ M ≤ 1` gives `0 ≤ 1_a ⊗ M ≤ 1`. -/
theorem isEffect_sysLift {M : EndM (QubitCells L₁) (univ : Finset L₁)}
    (hM : IsEffect M) : IsEffect (sysLift (L₂ := L₂) M) :=
  ⟨(LinearMap.nonneg_iff_isPositive _).mpr (isPositive_sysLift hM.isPositive),
    le_of_le_of_eq (sysLift_mono hM.2) sysLift_one⟩

theorem sysLift_smul (c : ℂ) (M : EndM (QubitCells L₁) (univ : Finset L₁)) :
    sysLift (L₂ := L₂) (c • M) = c • sysLift (L₂ := L₂) M := by
  rw [sysLift, sysLift, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [LinearMap.smul_comp, LinearMap.comp_smul]

/-- The lift collapses on an embedded state: the pattern is preserved and the
block operator acts on the system factor. -/
theorem sysLift_apply_emb (M : EndM (QubitCells L₁) (univ : Finset L₁))
    (e : L₂ → Bool) (w : HS (QubitCells L₁) (univ : Finset L₁)) :
    sysLift (L₂ := L₂) M (ancEmbed (L₁ := L₁) e w)
      = ancEmbed (L₁ := L₁) e (M w) := by
  rw [sysLift_apply]
  have key : ∀ e' : L₂ → Bool,
      ancEmbed (L₁ := L₁) (L₂ := L₂) e'
        (M (LinearMap.adjoint (ancEmbed (L₁ := L₁) (L₂ := L₂) e')
          (ancEmbed (L₁ := L₁) e w)))
      = if e' = e then ancEmbed (L₁ := L₁) e (M w) else 0 := by
    intro e'
    rw [adjoint_ancEmbed_comp]
    by_cases h : e' = e
    · rw [if_pos h, if_pos h, h]
    · rw [if_neg h, if_neg h, map_zero, map_zero]
  rw [Finset.sum_congr rfl fun e' _ => key e',
    Finset.sum_ite_eq' univ e (fun _ => ancEmbed (L₁ := L₁) e (M w)), if_pos (mem_univ _)]

/-- The expectation collapse at an embedded state. -/
theorem inner_emb_sysLift (M : EndM (QubitCells L₁) (univ : Finset L₁))
    (e : L₂ → Bool) (u w : HS (QubitCells L₁) (univ : Finset L₁)) :
    (⟪ancEmbed (L₁ := L₁) (L₂ := L₂) e u, sysLift (L₂ := L₂) M
        (ancEmbed (L₁ := L₁) e w)⟫ : ℂ) = ⟪u, M w⟫ := by
  rw [sysLift_apply_emb, inner_ancEmbed, if_pos rfl]

end SysLift

/-! ## §5. The (Ax-Init) display on the ancilla block -/

section InitBlock

variable {L₁ L₂ : Type*} [Fintype L₁] [DecidableEq L₁] [Fintype L₂] [DecidableEq L₂]

variable (L₁ L₂) in
/-- The ancilla block, as a cell set of the sum world. -/
def ancCells : Finset (L₁ ⊕ L₂) := Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

theorem mem_ancCells_inr (a : L₂) : (Sum.inr a : L₁ ⊕ L₂) ∈ ancCells L₁ L₂ :=
  Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩

theorem not_mem_ancCells_inl (s : L₁) : (Sum.inl s : L₁ ⊕ L₂) ∉ ancCells L₁ L₂ := by
  intro h
  obtain ⟨a, -, hc⟩ := Finset.mem_map.mp h
  exact absurd hc (by simp)

/-- The Boolean pattern stored by a classical state of the ancilla block. -/
def ancPat (q : QIdx (QubitCells (L₁ ⊕ L₂)) (ancCells L₁ L₂)) : L₂ → Bool :=
  fun a => q ⟨Sum.inr a, mem_ancCells_inr a⟩

/-- Classical states of the ancilla block are total Boolean patterns. -/
def ancPatEquiv : QIdx (QubitCells (L₁ ⊕ L₂)) (ancCells L₁ L₂) ≃ (L₂ → Bool) where
  toFun := ancPat
  invFun e i :=
    match i with
    | ⟨Sum.inl s, h⟩ => absurd h (not_mem_ancCells_inl s)
    | ⟨Sum.inr a, _⟩ => e a
  left_inv q := by
    funext i
    obtain ⟨i, hi⟩ := i
    cases i with
    | inl s => exact absurd hi (not_mem_ancCells_inl s)
    | inr a => rfl
  right_inv e := rfl

theorem ancPat_default :
    ancPat (default : QIdx (QubitCells (L₁ ⊕ L₂)) (ancCells L₁ L₂))
      = fun _ => false := rfl

/-- **The Kraus operators of the ancilla initialisation are pattern
resets**: `E_q = ∣0…0⟩⟨q∣_a ⊗ 1 = ancEmbed 0…0 ∘ₗ (ancEmbed q)†`. -/
theorem initKraus_ancCells (q : QIdx (QubitCells (L₁ ⊕ L₂)) (ancCells L₁ L₂)) :
    initKraus (QubitCells (L₁ ⊕ L₂)) (ancCells L₁ L₂) q
      = ancEmbed (L₁ := L₁) (L₂ := L₂) (fun _ => false) ∘ₗ
          LinearMap.adjoint (ancEmbed (L₁ := L₁) (L₂ := L₂) (ancPat q)) := by
  refine LinearMap.ext fun w => ?_
  conv_lhs => rw [qubitHS_expand (L := L₁ ⊕ L₂) w]
  conv_rhs => rw [qubitHS_expand (L := L₁ ⊕ L₂) w]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, map_smul]
  refine congrArg (_ • ·) ?_
  -- the right-hand side on the basis ket of `g`, in closed form
  have hRHS : (ancEmbed (L₁ := L₁) (L₂ := L₂) (fun _ => false) ∘ₗ
      LinearMap.adjoint (ancEmbed (L₁ := L₁) (L₂ := L₂) (ancPat q)))
        (deltav (QubitCells (L₁ ⊕ L₂)) (qbIdx (L₁ ⊕ L₂) g))
      = if ancPat q = (fun a => g (Sum.inr a))
        then deltav (QubitCells (L₁ ⊕ L₂))
          (qbIdx (L₁ ⊕ L₂) (Sum.elim (fun s => g (Sum.inl s)) fun _ => false))
        else 0 := by
    rw [LinearMap.comp_apply, deltav_eq_ancEmbed g, adjoint_ancEmbed_comp]
    by_cases h : ancPat q = fun a => g (Sum.inr a)
    · rw [if_pos h, if_pos h, ancEmbed_deltav]
    · rw [if_neg h, if_neg h, map_zero]
  rw [hRHS]
  by_cases hpat : ancPat q = fun a => g (Sum.inr a)
  · rw [if_pos hpat]
    -- the ancilla pattern matches `q`: the block is reset to all-zero and the
    -- system block is untouched
    have hres : QIdx.res (QubitCells (L₁ ⊕ L₂)) (subset_univ (ancCells L₁ L₂))
        (qbIdx (L₁ ⊕ L₂) g) = q := by
      funext i
      obtain ⟨i, hi⟩ := i
      cases i with
      | inl s => exact absurd hi (not_mem_ancCells_inl s)
      | inr a => exact (congrFun hpat a).symm
    refine PiLp.ext fun l => ?_
    have hdd := dv_dot (D := QubitCells (L₁ ⊕ L₂)) q q
    rw [initKraus, liftF_deltav_apply, hres, outerLM_apply, hdd, if_pos rfl, one_smul]
    rw [deltav_apply, deltav_apply]
    by_cases hl : l = qbIdx (L₁ ⊕ L₂)
        (Sum.elim (fun s => g (Sum.inl s)) fun _ => false)
    · subst hl
      rw [if_pos rfl]
      have h1 : QIdx.res (QubitCells (L₁ ⊕ L₂)) (subset_univ (ancCells L₁ L₂))
          (qbIdx (L₁ ⊕ L₂) (Sum.elim (fun s => g (Sum.inl s)) fun _ => false))
          = (default : QIdx (QubitCells (L₁ ⊕ L₂)) (ancCells L₁ L₂)) := by
        funext i
        obtain ⟨i, hi⟩ := i
        cases i with
        | inl s => exact absurd hi (not_mem_ancCells_inl s)
        | inr a => rfl
      have h2 : QIdx.res (QubitCells (L₁ ⊕ L₂))
          (sdiff_subset : (univ : Finset (L₁ ⊕ L₂)) \ ancCells L₁ L₂ ⊆ univ)
          (qbIdx (L₁ ⊕ L₂) (Sum.elim (fun s => g (Sum.inl s)) fun _ => false))
          = QIdx.res (QubitCells (L₁ ⊕ L₂)) sdiff_subset (qbIdx (L₁ ⊕ L₂) g) := by
        funext i
        obtain ⟨i, hi⟩ := i
        cases i with
        | inl s => rfl
        | inr a => exact absurd (mem_ancCells_inr a) (Finset.mem_sdiff.mp hi).2
      rw [h1, if_pos rfl, h2, if_pos rfl]
      norm_num
    · rw [if_neg hl]
      -- one of the two indicator factors on the left vanishes
      by_cases hz : QIdx.res (QubitCells (L₁ ⊕ L₂)) (subset_univ (ancCells L₁ L₂)) l
          = (default : QIdx (QubitCells (L₁ ⊕ L₂)) (ancCells L₁ L₂))
      · rw [if_pos hz]
        rw [if_neg, mul_zero]
        intro hc
        refine hl ?_
        funext i
        obtain ⟨i, hi⟩ := i
        cases i with
        | inl s =>
            exact congrFun hc ⟨Sum.inl s,
              Finset.mem_sdiff.mpr ⟨mem_univ _, not_mem_ancCells_inl s⟩⟩
        | inr a =>
            exact congrFun hz ⟨Sum.inr a, mem_ancCells_inr a⟩
      · rw [if_neg hz, zero_mul]
  · rw [if_neg hpat]
    -- the left-hand side dies on the ancilla-pattern mismatch
    refine PiLp.ext fun l => ?_
    have hdd := dv_dot (D := QubitCells (L₁ ⊕ L₂)) q
      (QIdx.res (QubitCells (L₁ ⊕ L₂)) (subset_univ (ancCells L₁ L₂)) (qbIdx (L₁ ⊕ L₂) g))
    rw [initKraus, liftF_deltav_apply, outerLM_apply, hdd]
    rw [if_neg, zero_smul]
    · simp
    · intro hc
      exact hpat (funext fun a => congrFun hc ⟨Sum.inr a, mem_ancCells_inr a⟩)

variable {σT : Type*}

/-- **The (Ax-Init) display on the ancilla block**: the initialisation
transformer of the ancilla cell set is the system-operator lift of the
vacuum block, `E†(A) = 1_a ⊗ (⟨0…0∣_a A ∣0…0⟩_a)`.  This is what turns a
vacuum-sector compression into a valid global precondition. -/
theorem initPre_ancCells_op (A : Assn σT (QubitCells (L₁ ⊕ L₂))) (σ : σT) :
    (A.initPre fun _ => ancCells L₁ L₂).op σ
      = sysLift (L₂ := L₂)
          (LinearMap.adjoint (ancEmbed (L₁ := L₁) (L₂ := L₂) (fun _ => false)) ∘ₗ
            A.op σ ∘ₗ ancEmbed (L₁ := L₁) (L₂ := L₂) (fun _ => false)) := by
  rw [Assn.initPre_op_eq_sum, sysLift]
  refine Fintype.sum_equiv (ancPatEquiv (L₁ := L₁) (L₂ := L₂)) _ _ fun q => ?_
  rw [initKraus_ancCells q, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
  change (ancEmbed (L₁ := L₁) (L₂ := L₂) (ancPat q) ∘ₗ
      LinearMap.adjoint (ancEmbed (L₁ := L₁) (L₂ := L₂) fun _ => false)) ∘ₗ A.op σ ∘ₗ
      (ancEmbed (L₁ := L₁) (L₂ := L₂) (fun _ => false) ∘ₗ
        LinearMap.adjoint (ancEmbed (L₁ := L₁) (L₂ := L₂) (ancPat q))) = _
  simp only [LinearMap.comp_assoc]
  rfl

end InitBlock

end Qhl
