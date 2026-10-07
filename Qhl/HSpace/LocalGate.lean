import Qhl.Register.Basic

/-!
# Per-cell product states and one-site gates

A small generic tensor-algebra layer, ported from CoqQ:

* `prodV D ψ : HS D W` — the **per-cell product state** `⊗_{i ∈ W} ψ i`, the
  specialisation of CoqQ's `tenvm` (`hstensor.v:950`) to the family of
  singleton registers (CoqQ's `t2tv_tuple`/`tketTV` idiom). Unlike
  `tenvFamily` it needs no `biUnion`, no pairwise-disjointness side condition
  and no `packEquiv` reindexing: on `QIdx D W = ∀ i : ↥W, D i` the coefficient
  of the product state at a classical state is literally the product of the
  factors' coefficients.
* `prodV_split` — the CoqQ `tenvm`-splitting: a product state over `W` is the
  tensor of its restrictions to `S` and `W \ S`, up to the `liftF` cast.
* `singleIso`/`singleOp` — the one-site transport `EuclideanSpace ℂ (D a) ≃ₗᵢ
  HS D (Reg.single a).sig` and conjugation by it: CoqQ's `tv2v`/`tf2f`
  (`qmem.v:157`) for a one-cell register, with the `Fin 1`-tuple layer
  (`tupleOne`) folded in.
* `liftF_regOp_tenv`/`liftF_regOp_prodV` — **the arity-general block bridge**
  (CoqQ `lift_lf`, `hstensor.v:3390`, acting on a `tenvm`-split state): for a
  register of *any* arity `k` and *any* operator on its tuple space — the
  operator may **entangle** the cells of the block — the cylindrical extension
  acts as that operator on the block factor and fixes the complement. The
  output is in general *not* a product state, so the conclusion keeps the split
  (`tenv`) form.
* `liftF_singleOp_prodV` — **the one-site bridge**, the `k = 1` corollary of
  the block bridge: a lifted one-site operator acts on the one factor it names
  and fixes the others. This is CoqQ's `tentf_tuple_apply` (`hstensor.v`)
  composed with `lift_lf` (`hstensor.v:3390`), specialised to a single factor,
  where the block factor collapses back to a product state via
  `prodV_sig_single`.

Everything is generic in the world `L`, the cell types `D`, the ambient
register set `W`, the register arity and the operator; no gate and no example
fixture appears.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S W : Finset L}

/-! ## The per-cell product state (CoqQ `tenvm` on singleton registers) -/

/-- The product state `⊗_{i ∈ W} ψ i` of a family of one-cell states. CoqQ
`tenvm` (`hstensor.v:950`) specialised to singleton registers. -/
noncomputable def prodV (ψ : ∀ i, EuclideanSpace ℂ (D i)) : HS D W :=
  WithLp.toLp 2 fun l => ∏ i : ↥W, ψ (i : L) (l i)

/-- CoqQ's `\ten_i ψ` (`hstensor.v:950`) as a binder: `⨂ᵥ i, ψ i` is
`prodV _ (fun i => ψ i)`, the `ᵥ` suffix matching the binary `u ⊗ᵥ v`. The
cell-type family `D` and the ambient set `W` are inferred from the expected
`HS D W` type. -/
scoped syntax:max "⨂ᵥ " Lean.binderIdent ", " term:67 : term

scoped macro_rules
  | `(⨂ᵥ $i:ident, $ψ) => `(Qhl.prodV _ fun $i => $ψ)
  | `(⨂ᵥ _, $ψ) => `(Qhl.prodV _ fun _ => $ψ)

@[simp, HS_simps]
theorem prodV_apply (ψ : ∀ i, EuclideanSpace ℂ (D i)) (l : QIdx D W) :
    prodV D (W := W) ψ l = ∏ i : ↥W, ψ (i : L) (l i) := rfl

/-- Only the factors on `W` matter. -/
theorem prodV_congr {ψ φ : ∀ i, EuclideanSpace ℂ (D i)} (h : ∀ i ∈ W, ψ i = φ i) :
    prodV D (W := W) ψ = prodV D (W := W) φ :=
  PiLp.ext fun l => Finset.prod_congr rfl fun i _ => by rw [h (i : L) i.2]

/-- A product of computational basis kets is a computational basis ket. CoqQ
`t2tv_tuple` (`hstensor.v`). -/
theorem prodV_single (m : ∀ i, D i) :
    prodV D (W := W) (fun i => EuclideanSpace.single (m i) 1)
      = deltav D (fun i : ↥W => m (i : L)) := by
  refine PiLp.ext fun l => ?_
  rw [prodV_apply, deltav_apply]
  by_cases h : l = fun i : ↥W => m (i : L)
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i : ↥W, l i ≠ m (i : L) := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- CoqQ `tenvm_dot` (`hstensor.v:1237`) for singleton registers: the product
state multiplies inner products, factor by factor. -/
theorem prodV_inner (ψ φ : ∀ i, EuclideanSpace ℂ (D i)) :
    ⟪prodV D (W := W) ψ, prodV D (W := W) φ⟫ = ∏ i : ↥W, ⟪ψ (i : L), φ (i : L)⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, prodV_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_prod, ← Finset.prod_mul_distrib]

/-- CoqQ `tenvm_norm`: the norm of a product state is the product of the
norms. -/
theorem norm_prodV (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    ‖prodV D (W := W) ψ‖ = ∏ i : ↥W, ‖ψ (i : L)‖ := by
  have hnn : (0 : ℝ) ≤ ∏ i : ↥W, ‖ψ (i : L)‖ :=
    Finset.prod_nonneg fun i _ => norm_nonneg _
  have h : (⟪prodV D (W := W) ψ, prodV D (W := W) ψ⟫ : ℂ)
      = (((∏ i : ↥W, ‖ψ (i : L)‖ : ℝ) : ℂ)) ^ 2 := by
    rw [prodV_inner, Complex.ofReal_prod, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => inner_self_eq_norm_sq_to_K _
  have h2 : ((‖prodV D (W := W) ψ‖ : ℝ) : ℂ) ^ 2
      = ((∏ i : ↥W, ‖ψ (i : L)‖ : ℝ) : ℂ) ^ 2 :=
    (inner_self_eq_norm_sq_to_K _).symm.trans h
  have h3 : ‖prodV D (W := W) ψ‖ ^ 2 = (∏ i : ↥W, ‖ψ (i : L)‖) ^ 2 := by
    exact_mod_cast h2
  rw [← Real.sqrt_sq (norm_nonneg (prodV D (W := W) ψ)), ← Real.sqrt_sq hnn, h3]

/-- CoqQ's `tenvm` splitting: a product state over `W` is the tensor of its
restrictions to `S` and to `W \ S`, along the cast `S ∪ (W \ S) = W` that
`liftF` uses. -/
theorem prodV_split (h : S ⊆ W) (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    prodV D (W := W) ψ
      = castH D (union_sdiff_of_subset h)
          (tenv D (prodV D (W := S) ψ) (prodV D (W := W \ S) ψ)) := by
  refine PiLp.ext fun l => ?_
  classical
  obtain ⟨f, hfi⟩ : ∃ f : L → ℂ, ∀ (i : L) (hi : i ∈ W), f i = ψ i (l ⟨i, hi⟩) :=
    ⟨fun i => if hi : i ∈ W then ψ i (l ⟨i, hi⟩) else 1, fun i hi => dif_pos hi⟩
  have key : ∀ (T : Finset L) (hT : T ⊆ W) (k : QIdx D T),
      (∀ i : ↥T, k i = l ⟨(i : L), hT i.2⟩) →
        (∏ i : ↥T, ψ (i : L) (k i)) = ∏ i ∈ T, f i := by
    intro T hT k hk
    rw [← Finset.prod_coe_sort T f]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hk i, hfi (i : L) (hT i.2)]
  have e₀ := key W Finset.Subset.rfl l fun _ => rfl
  have e₁ := key S h (QIdx.res D subset_union_left
    (QIdx.cast D (union_sdiff_of_subset h).symm l)) fun _ => rfl
  have e₂ := key (W \ S) sdiff_subset (QIdx.res D subset_union_right
    (QIdx.cast D (union_sdiff_of_subset h).symm l)) fun _ => rfl
  simp only [prodV_apply, castH_apply, tenv_apply]
  rw [e₀, e₁, e₂, ← Finset.prod_sdiff h, mul_comm]

/-! ## One-cell register plumbing -/

namespace Reg

variable {D}

/-- Every cell of a one-cell register is *the* cell. -/
theorem mem_sig_single {a : L} (j : ↥(Reg.single a).sig) : (j : L) = a := by
  obtain ⟨i, hi⟩ := Reg.mem_sig.mp j.2
  exact hi.symm

/-- The cell of a one-cell register belongs to its signature. -/
theorem self_mem_sig_single (a : L) : a ∈ (Reg.single a).sig :=
  (Reg.single a).apply_mem_sig 0

variable (D)

/-- The classical state of a one-cell register carrying the value `v`. -/
noncomputable def singleIdx (a : L) (v : D a) : QIdx D (Reg.single a).sig :=
  (Reg.single a).idxEquiv D fun _ => v

@[simp]
theorem singleIdx_at (a : L) (ha : a ∈ (Reg.single a).sig) (v : D a) :
    singleIdx D a v ⟨a, ha⟩ = v := rfl

/-- A classical state of a one-cell register is the one carrying its value at
the cell. -/
theorem idxEquiv_single_const (a : L) (ha : a ∈ (Reg.single a).sig)
    (x : QIdx D (Reg.single a).sig) : singleIdx D a (x ⟨a, ha⟩) = x := by
  funext j
  obtain rfl : j = (⟨a, ha⟩ : ↥(Reg.single a).sig) := Subtype.ext (mem_sig_single j)
  rfl

theorem idxEquiv_single_symm (a : L) (ha : a ∈ (Reg.single a).sig)
    (x : QIdx D (Reg.single a).sig) :
    ((Reg.single a).idxEquiv D).symm x = fun _ => x ⟨a, ha⟩ :=
  (Equiv.symm_apply_eq _).mpr (idxEquiv_single_const D a ha x).symm

end Reg

/-- The restriction of an ambient classical state to a one-cell register, in
the register's own coordinates. -/
theorem res_single (a : L) (h : (Reg.single a).sig ⊆ W) (l : QIdx D W) :
    QIdx.res D h l = Reg.singleIdx D a (l ⟨a, h (Reg.self_mem_sig_single a)⟩) :=
  (Reg.idxEquiv_single_const D a (Reg.self_mem_sig_single a) (QIdx.res D h l)).symm

/-- Outside a one-cell register, agreement is agreement at every other cell of
the ambient set — the Kronecker factor of `liftF_deltav_apply`. -/
theorem res_sdiff_single_eq_iff (a : L) (l m : QIdx D W) :
    QIdx.res D (sdiff_subset : W \ (Reg.single a).sig ⊆ W) l
        = QIdx.res D sdiff_subset m
      ↔ ∀ (i : L) (hi : i ∈ W), i ≠ a → l ⟨i, hi⟩ = m ⟨i, hi⟩ := by
  constructor
  · intro hres i hi hia
    exact congrFun hres ⟨i, mem_sdiff.2 ⟨hi, fun hc => hia (Reg.mem_sig_single ⟨i, hc⟩)⟩⟩
  · intro hval
    funext j
    obtain ⟨hjW, hjS⟩ := mem_sdiff.1 j.2
    exact hval (j : L) hjW fun hc => hjS (by rw [hc]; exact Reg.self_mem_sig_single a)

/-! ## The one-site transport (CoqQ `tv2v`/`tf2f` for a one-cell register) -/

/-- The `Fin 1`-tuple layer: a one-cell state as a state of the tuple space of
the one-cell register. -/
noncomputable def tupleOne (a : L) :
    EuclideanSpace ℂ (D a) ≃ₗᵢ[ℂ] TSpace D (Reg.single a).toFun :=
  euclCongr (Equiv.funUnique (Fin 1) (D a)).symm

@[simp]
theorem tupleOne_apply (a : L) (w : EuclideanSpace ℂ (D a))
    (y : TIdx D (Reg.single a).toFun) : tupleOne D a w y = w (y default) := rfl

/-- CoqQ `tv2v` (`qmem.v:157`) for a one-cell register: the one-cell state
space is the labelled space of that cell. -/
noncomputable def singleIso (a : L) :
    EuclideanSpace ℂ (D a) ≃ₗᵢ[ℂ] HS D (Reg.single a).sig :=
  (tupleOne D a).trans ((Reg.single a).encode D)

theorem singleIso_apply (a : L) (ha : a ∈ (Reg.single a).sig)
    (w : EuclideanSpace ℂ (D a)) (x : QIdx D (Reg.single a).sig) :
    singleIso D a w x = w (x ⟨a, ha⟩) := by
  change tupleOne D a w (((Reg.single a).idxEquiv D).symm x) = _
  rw [tupleOne_apply, Reg.idxEquiv_single_symm D a ha]

/-- `singleIso` sends the one-cell basis kets to the register's basis kets. -/
@[simp]
theorem singleIso_single (a : L) (v : D a) :
    singleIso D a (EuclideanSpace.single v 1) = deltav D (Reg.singleIdx D a v) := by
  have ha := Reg.self_mem_sig_single a
  refine PiLp.ext fun x => ?_
  have hiff : x = Reg.singleIdx D a v ↔ x ⟨a, ha⟩ = v := by
    constructor
    · rintro rfl
      exact Reg.singleIdx_at D a ha v
    · intro hv
      rw [← Reg.idxEquiv_single_const D a ha x, hv]
  rw [singleIso_apply D a ha, deltav_apply,
    show (EuclideanSpace.single v (1 : ℂ)) (x ⟨a, ha⟩) = if x ⟨a, ha⟩ = v then 1 else 0 by simp]
  exact if_congr hiff.symm rfl rfl

/-- CoqQ `tf2f` (`qmem.v:157`) for a one-cell register: a one-cell operator as
an operator on the labelled space of that cell. -/
noncomputable def singleOp (a : L)
    (A : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) :
    EndM D (Reg.single a).sig :=
  (singleIso D a).toLinearEquiv.conj A

theorem singleOp_apply (a : L) (A : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a))
    (v : HS D (Reg.single a).sig) :
    singleOp D a A v = singleIso D a (A ((singleIso D a).symm v)) := rfl

@[simp]
theorem singleOp_singleIso (a : L)
    (A : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a))
    (w : EuclideanSpace ℂ (D a)) :
    singleOp D a A (singleIso D a w) = singleIso D a (A w) := by
  rw [singleOp_apply, LinearIsometryEquiv.symm_apply_apply]

/-- `Reg.op` of a one-cell register, on a gate presented on `EuclideanSpace ℂ
(D a)` through the `Fin 1`-tuple layer, is conjugation by `singleIso`. -/
theorem reg_op_single (a : L)
    (A : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) :
    (Reg.single a).op D ((tupleOne D a).toLinearEquiv.conj A) = singleOp D a A := rfl

/-- A one-cell gate, moved to the tuple space of the one-cell register — the
shape a program's one-cell unitary gate has. -/
noncomputable def singleGate (a : L) (U : UnitaryOp (EuclideanSpace ℂ (D a))) :
    UnitaryOp (TSpace D (Reg.single a).toFun) :=
  euclCongrOp (Equiv.funUnique (Fin 1) (D a)).symm U

/-- The bundled-gate presentation of `reg_op_single`. -/
theorem reg_op_singleGate (a : L) (U : UnitaryOp (EuclideanSpace ℂ (D a))) :
    (Reg.single a).op D (singleGate D a U)
      = singleOp D a (U : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) := rfl

/-- Matrix entries of a one-site operator, in the register's coordinates. -/
theorem singleOp_deltav_apply (a : L)
    (A : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) (v w : D a) :
    singleOp D a A (deltav D (Reg.singleIdx D a v)) (Reg.singleIdx D a w)
      = A (EuclideanSpace.single v 1) w := by
  rw [← singleIso_single, singleOp_singleIso,
    singleIso_apply D a (Reg.self_mem_sig_single a), Reg.singleIdx_at]

/-- Matrix entries of a **lifted** one-site operator (CoqQ `lift_lf`,
`hstensor.v:3390`): the one-cell entry at the two values of the cell, times the
Kronecker delta on every other cell. -/
theorem liftF_singleOp_deltav_apply (a : L) (h : (Reg.single a).sig ⊆ W)
    (A : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) (m l : QIdx D W) :
    liftF D h (singleOp D a A) (deltav D m) l
      = A (EuclideanSpace.single (m ⟨a, h (Reg.self_mem_sig_single a)⟩) 1)
            (l ⟨a, h (Reg.self_mem_sig_single a)⟩)
        * (if QIdx.res D (sdiff_subset : W \ (Reg.single a).sig ⊆ W) l
              = QIdx.res D sdiff_subset m then 1 else 0) := by
  rw [liftF_deltav_apply, res_single, res_single, singleOp_deltav_apply]

/-! ## The arity-general block bridge (CoqQ `lift_lf` on `tenvm`-split states) -/

/-- **The arity-general block bridge**, factored-vector form (CoqQ `lift_lf`,
`hstensor.v:3390`, acting on a `tenvm`-split state): for a register `r` of ANY
arity and any operator `A` on its tuple space — `A` may entangle the cells of
the block — the cylindrical extension of `r.op D A` acts as `A` on the
`r.sig`-block factor and fixes the complement. -/
theorem liftF_regOp_tenv {k : ℕ} (r : Reg L k) (h : r.sig ⊆ W)
    (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
    (v : HS D r.sig) (w : HS D (W \ r.sig)) :
    liftF D h (r.op D A) (castH D (union_sdiff_of_subset h) (tenv D v w))
      = castH D (union_sdiff_of_subset h) (tenv D (r.op D A v) w) :=
  liftF_castH_tenv D h (r.op D A) v w

/-- Bundled-unitary form of `liftF_regOp_tenv`. -/
theorem liftF_regGate_tenv {k : ℕ} (r : Reg L k) (h : r.sig ⊆ W)
    (U : UnitaryOp (TSpace D r.toFun)) (v : HS D r.sig) (w : HS D (W \ r.sig)) :
    liftF D h (r.op D (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun))
        (castH D (union_sdiff_of_subset h) (tenv D v w))
      = castH D (union_sdiff_of_subset h)
          (tenv D (r.op D (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) v) w) :=
  liftF_regOp_tenv D r h _ v w

/-- The arity-general block bridge on a product state: the input product state
splits into the `r.sig`-block and its complement (`prodV_split`), the block
transforms by `A`, the complement is fixed. The output is NOT in general a
product state — `A` may entangle the block — so the right-hand side keeps the
split form. -/
theorem liftF_regOp_prodV {k : ℕ} (r : Reg L k) (h : r.sig ⊆ W)
    (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    liftF D h (r.op D A) (prodV D (W := W) ψ)
      = castH D (union_sdiff_of_subset h)
          (tenv D (r.op D A (prodV D (W := r.sig) ψ))
            (prodV D (W := W \ r.sig) ψ)) := by
  rw [prodV_split D h ψ]
  exact liftF_regOp_tenv D r h A _ _

/-- Bundled-unitary form of `liftF_regOp_prodV`. -/
theorem liftF_regGate_prodV {k : ℕ} (r : Reg L k) (h : r.sig ⊆ W)
    (U : UnitaryOp (TSpace D r.toFun)) (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    liftF D h (r.op D (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)) (prodV D (W := W) ψ)
      = castH D (union_sdiff_of_subset h)
          (tenv D (r.op D (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)
              (prodV D (W := r.sig) ψ))
            (prodV D (W := W \ r.sig) ψ)) :=
  liftF_regOp_prodV D r h _ ψ

/-! ## The bridge: a one-site gate on one factor of a product state -/

/-- A product state factors as its one-cell factor at `a` tensored with the
rest. -/
theorem prodV_sig_single (a : L) (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    prodV D (W := (Reg.single a).sig) ψ = singleIso D a (ψ a) := by
  refine PiLp.ext fun x => ?_
  rw [prodV_apply, singleIso_apply D a (Reg.self_mem_sig_single a),
    Finset.prod_eq_single (⟨a, Reg.self_mem_sig_single a⟩ : ↥(Reg.single a).sig)]
  · intro j _ hj
    exact absurd (Subtype.ext (Reg.mem_sig_single j)) hj
  · intro hj
    exact absurd (Finset.mem_univ _) hj

/-- **The bridge** (CoqQ `tentf_tuple_apply` composed with `lift_lf`): a
one-site operator, lifted to the ambient register set, acts on the single
factor it names and leaves every other factor untouched. This is the `k = 1`
corollary of `liftF_regOp_prodV`: the block is `(Reg.single a).sig`, whose
factor collapses back to a one-cell state by `prodV_sig_single`. -/
theorem liftF_singleOp_prodV (a : L) (h : (Reg.single a).sig ⊆ W)
    (A : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a))
    (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    liftF D h (singleOp D a A) (prodV D (W := W) ψ)
      = prodV D (W := W) (Function.update ψ a (A (ψ a))) := by
  rw [← reg_op_single, liftF_regOp_prodV,
    prodV_split D h (Function.update ψ a (A (ψ a)))]
  refine congrArg (castH D (union_sdiff_of_subset h)) (congrArg₂ (tenv D) ?_ ?_)
  · rw [reg_op_single, prodV_sig_single, prodV_sig_single, Function.update_self,
      singleOp_singleIso]
  · refine prodV_congr D fun i hi => ?_
    have hia : i ≠ a := fun hc =>
      (mem_sdiff.1 hi).2 (by rw [hc]; exact Reg.self_mem_sig_single a)
    exact (Function.update_of_ne hia _ _).symm

/-- The bundled-unitary form of the bridge — the shape a program's one-cell
gate has (`Reg.single a` with a gate transported by
`euclCongrOp (Equiv.funUnique (Fin 1) (D a)).symm`, i.e. `singleGate`). -/
theorem liftF_singleGate_prodV (a : L) (h : (Reg.single a).sig ⊆ W)
    (U : UnitaryOp (EuclideanSpace ℂ (D a))) (ψ : ∀ i, EuclideanSpace ℂ (D i)) :
    liftF D h ((Reg.single a).op D (singleGate D a U)) (prodV D (W := W) ψ)
      = prodV D (W := W)
          (Function.update ψ a
            ((U : EuclideanSpace ℂ (D a) →ₗ[ℂ] EuclideanSpace ℂ (D a)) (ψ a))) := by
  rw [reg_op_singleGate, liftF_singleOp_prodV]

end Qhl
