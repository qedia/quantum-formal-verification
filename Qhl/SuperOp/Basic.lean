import Qhl.HSpace.Basic
import Qhl.Foundations.Order

/-!
# Super-operators: Kraus forms, trace conditions, duals, measurements

Spec 04 §2, milestone M6 phase 1 (items Q-1, Q-2, Q-3, Q-5, Q-6, Q-10), over
the fixtures of `Qhl/HSpace/Basic.lean`.

* `SuperOp D S T` — CoqQ `'SO(U,V)` (`quantum.v:2585-2609`), a plain
  abbreviation of `EndM D S →ₗ[ℂ] EndM D T`
* `kraussoOf`, `formsoOf` — Q-3, CoqQ `krausso:2886`, `formso:2918`
* `IsTP`, `IsTN` — Q-5, CoqQ `tpmap/tnmap:3184-3188`
* `dualSO`, `IsUnital` — Q-6, CoqQ `dualso:3414`, `'QU:3556`
* `IsTraceNincr`, `IsQMeasure` — Q-10, CoqQ `'TN/'QM:3022-3048`

Q-2 (`denlf/den1lf`, `quantum.v:350,380`) is already covered by
`Qhl/Foundations/Basic.lean`'s `IsDensity`/`IsDensity1`; the literal CoqQ
trace-bound form is the bridge `isDensity_iff` there.

`IsQO`/`IsQC` (CoqQ `'QO/'QC:3497-3527`) are `IsCP ∧ IsTN` / `IsCP ∧ IsTP`;
`IsCP` is Choi-based (Q-4) and lands in the Choi file of phase 2 together with
those two bundles. Only the trace halves are defined here.

Traces are spelled plainly as `LinearMap.trace ℂ (HS D S)`; no extra notation.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace ComplexOrder

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S T U : Finset L}
variable {κ κ₁ κ₂ : Type*} [Fintype κ] [Fintype κ₁] [Fintype κ₂]

/-! ## Q-1: the super-operator type -/

/-- Super-operators between labelled operator spaces. CoqQ: `'SO(U,V)`
(`quantum.v:2585-2609`; CoqQ wraps in a `Variant`, we use a plain abbreviation
per spec 04 §2, so the module structure and composition come from mathlib). -/
abbrev SuperOp (S T : Finset L) : Type _ := EndM D S →ₗ[ℂ] EndM D T

/-! ## Sum-pushing through `∘ₗ` (local helpers; this mathlib pin lacks
`LinearMap.sum_comp`/`comp_sum`) -/

private theorem sumLM_comp {ι : Type*} {A B C : Finset L} (s : Finset ι)
    (f : ι → LinM D B C) (g : LinM D A B) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, LinearMap.zero_comp]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, LinearMap.add_comp, ih]

private theorem comp_sumLM {ι : Type*} {A B C : Finset L} (s : Finset ι)
    (g : LinM D B C) (f : ι → LinM D A B) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, LinearMap.comp_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, LinearMap.comp_add, ih]

/-! ## Basis extensionality on `EndM` (Q-6 support)

`EndM D S` is spanned by the "matrix units" `outerLM (deltav k) (deltav l)`
(`eq_sum_outerLM`/`outerLM_ext` in `Qhl/Foundations/Basic.lean`); we
specialize to the `deltav` basis, and derive nondegeneracy of the trace
pairing `(x, M) ↦ Tr (x ∘ M)`. -/

/-- Linear maps out of `EndM D S` agreeing on all
`outerLM (deltav k) (deltav l)` are equal (spec 04, Q-6 support; specializes
`outerLM_ext` to the `deltav` basis). -/
theorem endM_ext_outer {W : Type*} [AddCommMonoid W] [Module ℂ W]
    {Φ Ψ : EndM D S →ₗ[ℂ] W}
    (h : ∀ k l, Φ (outerLM (deltav D k) (deltav D l))
      = Ψ (outerLM (deltav D k) (deltav D l))) :
    Φ = Ψ :=
  outerLM_ext (EuclideanSpace.basisFun (QIdx D S) ℂ)
    (EuclideanSpace.basisFun (QIdx D S) ℂ) fun k l => by
      simpa only [EuclideanSpace.basisFun_apply, deltav_def] using h k l

/-- Nondegeneracy of the trace pairing on `EndM` (Q-5/Q-6 support): operators
with equal pairings `Tr (x ∘ M)` against every `x` are equal. -/
theorem endM_ext_of_trace_comp {M N : EndM D S}
    (h : ∀ x : EndM D S,
      LinearMap.trace ℂ (HS D S) (x ∘ₗ M) = LinearMap.trace ℂ (HS D S) (x ∘ₗ N)) :
    M = N := by
  refine linM_ext D fun k => cdvP D fun l => ?_
  have hkl := h (outerLM (deltav D k) (deltav D l))
  rw [trace_outerLM_comp, trace_outerLM_comp] at hkl
  simpa [deltav, EuclideanSpace.inner_single_left] using hkl

/-! ## Q-3: Kraus-form super-operators -/

/-- The Kraus-form super-operator of an operator family:
`x ↦ ∑ i, f i ∘ₗ x ∘ₗ (f i)†`. CoqQ: `krausso` (`quantum.v:2886`). -/
noncomputable def kraussoOf (f : κ → LinM D S T) : SuperOp D S T where
  toFun x := ∑ i, f i ∘ₗ x ∘ₗ LinearMap.adjoint (f i)
  map_add' x y := by
    simp only [LinearMap.add_comp, LinearMap.comp_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply, Finset.smul_sum]

@[simp]
theorem kraussoOf_apply (f : κ → LinM D S T) (x : EndM D S) :
    kraussoOf D f x = ∑ i, f i ∘ₗ x ∘ₗ LinearMap.adjoint (f i) := rfl

/-- The single-operator ("form") super-operator `x ↦ f ∘ₗ x ∘ₗ f†`.
CoqQ: `formso` (`quantum.v:2918`). -/
noncomputable def formsoOf (f : LinM D S T) : SuperOp D S T :=
  kraussoOf D fun _ : Unit => f

/-- `formsoOf` is the `Unit`-indexed Kraus map. -/
theorem formsoOf_eq_kraussoOf (f : LinM D S T) :
    formsoOf D f = kraussoOf D fun _ : Unit => f := rfl

@[simp]
theorem formsoOf_apply (f : LinM D S T) (x : EndM D S) :
    formsoOf D f x = f ∘ₗ x ∘ₗ LinearMap.adjoint f := by
  simp [formsoOf]

/-- Kraus maps preserve positivity (Q-3 support; cf. CoqQ `krausso`
`quantum.v:2886`). -/
theorem kraussoOf_isPositive (f : κ → LinM D S T) {x : EndM D S}
    (hx : x.IsPositive) : (kraussoOf D f x).IsPositive := by
  rw [kraussoOf_apply]
  exact LinearMap.isPositive_sum _ fun i _ => hx.conj_adjoint (f i)

/-- The identity super-operator is `formsoOf 1`; CoqQ `formso1`-analogue
(the `idso` of `quantum.v:2609` in Kraus form). -/
theorem formsoOf_one : formsoOf D (1 : EndM D S) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp [Module.End.one_eq_id]

/-- Composition of Kraus maps is the Kraus map of the pairwise compositions
(CoqQ `comp_krausso`-analogue, Q-3 support). -/
theorem kraussoOf_comp (f : κ₁ → LinM D T U) (g : κ₂ → LinM D S T) :
    kraussoOf D f ∘ₗ kraussoOf D g
      = kraussoOf D fun p : κ₁ × κ₂ => f p.1 ∘ₗ g p.2 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, kraussoOf_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sumLM_comp, comp_sumLM]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.adjoint_comp]
  simp only [LinearMap.comp_assoc]

/-! ## Q-5: trace-preserving and trace-nonincreasing maps -/

/-- Trace-preserving super-operator. CoqQ: `tpmap` (`quantum.v:3184`). -/
def IsTP (E : SuperOp D S T) : Prop :=
  ∀ x : EndM D S, LinearMap.trace ℂ (HS D T) (E x) = LinearMap.trace ℂ (HS D S) x

/-- Trace-nonincreasing (on positive inputs) super-operator, `≤` from the
scoped `ComplexOrder`. CoqQ: `tnmap` (`quantum.v:3188`). -/
def IsTN (E : SuperOp D S T) : Prop :=
  ∀ x : EndM D S, x.IsPositive →
    LinearMap.trace ℂ (HS D T) (E x) ≤ LinearMap.trace ℂ (HS D S) x

theorem IsTP.isTN {E : SuperOp D S T} (h : IsTP D E) : IsTN D E :=
  fun x _ => (h x).le

/-- The identity super-operator is trace-preserving (Q-1 note: `idso` of
CoqQ `quantum.v:2609` is `LinearMap.id`). -/
theorem isTP_id : IsTP D (LinearMap.id : SuperOp D S S) := fun _ => rfl

theorem IsTP.comp {E : SuperOp D T U} {F : SuperOp D S T}
    (hE : IsTP D E) (hF : IsTP D F) : IsTP D (E ∘ₗ F) := fun x => by
  rw [LinearMap.comp_apply, hE, hF]

/-- Composition of trace-nonincreasing maps is trace-nonincreasing, provided
the inner map preserves positivity (automatic once CP is available in
phase 2; CoqQ composes at the `'QO` level, `quantum.v:3497`). -/
theorem IsTN.comp {E : SuperOp D T U} {F : SuperOp D S T}
    (hE : IsTN D E) (hF : IsTN D F)
    (hFpos : ∀ x : EndM D S, x.IsPositive → (F x).IsPositive) :
    IsTN D (E ∘ₗ F) := fun x hx =>
  le_trans (hE (F x) (hFpos x hx)) (hF x hx)

/-- Trace of a Kraus map's output as a trace pairing with `∑ i, (f i)† ∘ f i`
(Q-5 support; the trace-cyclicity core of CoqQ `krausso_tp/tn`). -/
theorem trace_kraussoOf (f : κ → LinM D S T) (x : EndM D S) :
    LinearMap.trace ℂ (HS D T) (kraussoOf D f x)
      = LinearMap.trace ℂ (HS D S) (x ∘ₗ ∑ i, LinearMap.adjoint (f i) ∘ₗ f i) := by
  rw [kraussoOf_apply, map_sum, comp_sumLM, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_comp_comm' (x ∘ₗ LinearMap.adjoint (f i)) (f i),
    LinearMap.comp_assoc]

/-- CoqQ `krausso_tp`-analogue (Q-5): a Kraus map is trace-preserving iff its
family satisfies the completeness relation `∑ i, (f i)† ∘ f i = 1`. -/
theorem kraussoOf_isTP_iff (f : κ → LinM D S T) :
    IsTP D (kraussoOf D f) ↔ ∑ i, LinearMap.adjoint (f i) ∘ₗ f i = 1 := by
  constructor
  · intro h
    refine endM_ext_of_trace_comp D fun x => ?_
    rw [← trace_kraussoOf, h x, Module.End.one_eq_id, LinearMap.comp_id]
  · intro h x
    rw [trace_kraussoOf, h, Module.End.one_eq_id, LinearMap.comp_id]

/-- CoqQ `krausso_tn`-analogue (Q-5): a Kraus map is trace-nonincreasing iff
`∑ i, (f i)† ∘ f i ≤ 1` in the Löwner order. -/
theorem kraussoOf_isTN_iff (f : κ → LinM D S T) :
    IsTN D (kraussoOf D f) ↔ ∑ i, LinearMap.adjoint (f i) ∘ₗ f i ≤ 1 := by
  constructor
  · intro h
    rw [le_iff_inner_le]
    intro v
    have hv := h (outerLM v v) (isPositive_outerLM_self v)
    rw [trace_kraussoOf, trace_outerLM_comp, trace_outerLM] at hv
    simpa only [Module.End.one_apply] using hv
  · intro h x hx
    rw [trace_kraussoOf]
    calc LinearMap.trace ℂ (HS D S) (x ∘ₗ ∑ i, LinearMap.adjoint (f i) ∘ₗ f i)
        ≤ LinearMap.trace ℂ (HS D S) (x ∘ₗ 1) := trace_comp_mono hx h
      _ = LinearMap.trace ℂ (HS D S) x := by
          rw [Module.End.one_eq_id, LinearMap.comp_id]

/-! ## Q-6: the dual super-operator -/

/-- The dual super-operator, defined by a concrete basis sum (avoiding a
Frobenius inner-product instance): the `(l,k)` matrix-unit coefficient of
`dualSO E A` is `Tr (E |δₖ⟩⟨δₗ| ∘ A)`. CoqQ: `dualso` (`quantum.v:3414`). -/
noncomputable def dualSO (E : SuperOp D S T) : SuperOp D T S where
  toFun A := ∑ k, ∑ l,
    LinearMap.trace ℂ (HS D T) (E (outerLM (deltav D k) (deltav D l)) ∘ₗ A) •
      outerLM (deltav D l) (deltav D k)
  map_add' A B := by
    simp only [LinearMap.comp_add, map_add, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    simp only [LinearMap.comp_smul, map_smul, smul_eq_mul, RingHom.id_apply, mul_smul,
      Finset.smul_sum]

theorem dualSO_apply (E : SuperOp D S T) (A : EndM D T) :
    dualSO D E A = ∑ k, ∑ l,
      LinearMap.trace ℂ (HS D T) (E (outerLM (deltav D k) (deltav D l)) ∘ₗ A) •
        outerLM (deltav D l) (deltav D k) := rfl

/-- **The defining property of the dual** (CoqQ `dualso_trlfE`,
`quantum.v:3437`): `Tr (x ∘ dualSO E A) = Tr (E x ∘ A)`. -/
theorem trace_comp_dualSO (E : SuperOp D S T) (A : EndM D T) (x : EndM D S) :
    LinearMap.trace ℂ (HS D S) (x ∘ₗ dualSO D E A)
      = LinearMap.trace ℂ (HS D T) (E x ∘ₗ A) := by
  have key : LinearMap.trace ℂ (HS D S) ∘ₗ LinearMap.lcomp ℂ (HS D S) (dualSO D E A)
      = LinearMap.trace ℂ (HS D T) ∘ₗ LinearMap.lcomp ℂ (HS D T) A ∘ₗ E := by
    refine endM_ext_outer D fun k l => ?_
    simp only [LinearMap.comp_apply, LinearMap.lcomp_apply']
    rw [trace_outerLM_comp, dualSO_apply]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, outerLM_apply, inner_sum,
      inner_smul_right, dv_dot]
    rw [Fintype.sum_eq_single k fun p hp =>
      Finset.sum_eq_zero fun q _ => by simp [hp]]
    rw [Fintype.sum_eq_single l fun q hq => by simp [Ne.symm hq]]
    simp
  simpa only [LinearMap.comp_apply, LinearMap.lcomp_apply'] using
    LinearMap.congr_fun key x

/-- Uniqueness: any super-operator with the trace-pairing property *is* the
dual (Q-6 support). -/
theorem eq_dualSO_of_trace {E : SuperOp D S T} {G : SuperOp D T S}
    (h : ∀ (x : EndM D S) (A : EndM D T),
      LinearMap.trace ℂ (HS D S) (x ∘ₗ G A) = LinearMap.trace ℂ (HS D T) (E x ∘ₗ A)) :
    G = dualSO D E :=
  LinearMap.ext fun A => endM_ext_of_trace_comp D fun x =>
    (h x A).trans (trace_comp_dualSO D E A x).symm

/-- CoqQ `dualsoK` (`quantum.v:3455`): the dual is involutive. -/
theorem dualSO_dualSO (E : SuperOp D S T) : dualSO D (dualSO D E) = E :=
  (eq_dualSO_of_trace D fun x A => by
    rw [LinearMap.trace_comp_comm', ← trace_comp_dualSO, LinearMap.trace_comp_comm']).symm

/-- CoqQ `dualso_krausE` (`quantum.v:3444`): the dual of a Kraus map is the
Kraus map of the adjoint family. -/
theorem dualSO_kraussoOf (f : κ → LinM D S T) :
    dualSO D (kraussoOf D f) = kraussoOf D fun i => LinearMap.adjoint (f i) := by
  refine (eq_dualSO_of_trace D fun x A => ?_).symm
  simp only [kraussoOf_apply, LinearMap.adjoint_adjoint]
  rw [comp_sumLM, sumLM_comp, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [← LinearMap.comp_assoc]
  rw [LinearMap.trace_comp_comm' (f i)]
  simp only [← LinearMap.comp_assoc]

/-- `dualSO` is additive in the super-operator (Q-6; `dualso` is linear,
CoqQ `quantum.v:3414`). -/
theorem dualSO_add (E F : SuperOp D S T) :
    dualSO D (E + F) = dualSO D E + dualSO D F :=
  (eq_dualSO_of_trace D fun x A => by
    simp only [LinearMap.add_apply, LinearMap.comp_add, LinearMap.add_comp, map_add,
      trace_comp_dualSO]).symm

/-- `dualSO` is ℂ-homogeneous in the super-operator (Q-6). -/
theorem dualSO_smul (c : ℂ) (E : SuperOp D S T) :
    dualSO D (c • E) = c • dualSO D E :=
  (eq_dualSO_of_trace D fun x A => by
    simp only [LinearMap.smul_apply, LinearMap.comp_smul, LinearMap.smul_comp, map_smul,
      trace_comp_dualSO]).symm

/-- Unital super-operator: preserves the identity. Stated for general
source/target registers (CoqQ's `'QU` is the endo case, `quantum.v:3556`). -/
def IsUnital (E : SuperOp D S T) : Prop := E 1 = 1

/-- CoqQ `'QU` duality (`quantum.v:3556`): the dual is unital iff the map is
trace-preserving. -/
theorem isUnital_dualSO_iff (E : SuperOp D S T) :
    IsUnital D (dualSO D E) ↔ IsTP D E := by
  constructor
  · intro h x
    have hx := trace_comp_dualSO D E 1 x
    rw [h] at hx
    simpa only [Module.End.one_eq_id, LinearMap.comp_id] using hx.symm
  · intro h
    refine endM_ext_of_trace_comp D fun x => ?_
    rw [trace_comp_dualSO]
    simp only [Module.End.one_eq_id, LinearMap.comp_id]
    exact h x

theorem IsTP.isUnital_dualSO {E : SuperOp D S T} (h : IsTP D E) :
    IsUnital D (dualSO D E) :=
  (isUnital_dualSO_iff D E).mpr h

/-! ## Q-10: measurement families -/

/-- Trace-nonincreasing operator family: `∑ i, (f i)† ∘ f i ≤ 1` in the
Löwner order. CoqQ: `'TN` (`quantum.v:3022`). -/
def IsTraceNincr (f : κ → LinM D S T) : Prop :=
  ∑ i, LinearMap.adjoint (f i) ∘ₗ f i ≤ 1

/-- Quantum measurement family: `∑ i, (f i)† ∘ f i = 1`.
CoqQ: `'QM` (`quantum.v:3048`). -/
def IsQMeasure (f : κ → LinM D S T) : Prop :=
  ∑ i, LinearMap.adjoint (f i) ∘ₗ f i = 1

theorem IsQMeasure.isTraceNincr {f : κ → LinM D S T} (h : IsQMeasure D f) :
    IsTraceNincr D f := le_of_eq h

/-- Bridge to Q-5: a measurement family induces a trace-preserving Kraus map
(CoqQ `'QM`/`krausso_tp`, `quantum.v:3048`). -/
theorem IsQMeasure.isTP_kraussoOf {f : κ → LinM D S T} (h : IsQMeasure D f) :
    IsTP D (kraussoOf D f) := (kraussoOf_isTP_iff D f).mpr h

/-- Bridge to Q-5: a trace-nonincreasing family induces a trace-nonincreasing
Kraus map (CoqQ `'TN`/`krausso_tn`, `quantum.v:3022`). -/
theorem IsTraceNincr.isTN_kraussoOf {f : κ → LinM D S T} (h : IsTraceNincr D f) :
    IsTN D (kraussoOf D f) := (kraussoOf_isTN_iff D f).mpr h

end Qhl
