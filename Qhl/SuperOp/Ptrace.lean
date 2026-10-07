import Qhl.SuperOp.Choi
import Qhl.HSpace.DotF

/-!
# Super-operators: the partial trace

Spec 04 §2, milestone M6 phase 3 (item Q-8), over the phase-1/2 API of
`Qhl/SuperOp/{Basic,Choi}.lean`.

* `ptraceKraus D W m` — the Kraus operator `(1_{S\W} ⊗ᶠ ⟨δ_m|)` of the partial
  trace, read off CoqQ `ptraceso_krausso` (`hstensor.v:3282`)
* `ptraceLM D W : SuperOp D S (S \ W)` — Q-8, CoqQ `ptraceso`
  (`hstensor.v:3259`), *defined* as the Kraus map of that family (so the CoqQ
  Kraus form `ptraceLM_eq_kraussoOf` is definitional), with the concrete
  matrix-entry model of spec 04 recovered as `ptraceLM_deltav_apply`:
  `(ptraceLM W f) δ_k` at `l` is `∑ m : QIdx D (S ∩ W), f_(merge k m, merge l m)`
* `ptraceKraus_isQMeasure` — the resolution-of-identity completeness relation
* **`ptraceLM_isQC`** — M6 acceptance item: the partial trace is a quantum
  channel; CoqQ `ptraceso_qc` (`hstensor.v:3303`)
* `ptrace_trace` — the partial trace preserves the full trace

Deferred (not an acceptance item): the composition law CoqQ `ptraceso_comp`
(`hstensor.v:3326`), `ptraceLM W₂ ∘ₗ ptraceLM W₁ = castSO (ptraceLM (W₁ ∪ W₂))`;
it needs a `castSO` cast-of-super-operators layer plus a reindexing bijection
`QIdx ((S\W₁)∩W₂) × QIdx (S∩W₁) ≃ QIdx (S∩(W₁∪W₂))` that nothing downstream
consumes yet.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace ComplexOrder

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S : Finset L}

/-! ## Sum-pushing helper (local clone, as in `Qhl/SuperOp/Tenso.lean`) -/

private theorem tenf_sum_right {S₁ S₂ T₁ T₂ : Finset L}
    {ι : Type*} (s : Finset ι) (f : LinM D S₁ T₁) (g : ι → LinM D S₂ T₂) :
    tenf D f (∑ i ∈ s, g i) = ∑ i ∈ s, tenf D f (g i) := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, tenf_zero_right]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, tenf_add_right, ih]

/-! ## Q-8: the Kraus family of the partial trace -/

/-- The Kraus operator of the partial trace at the classical state `m` of the
traced-out register `S ∩ W`: the identity on `S \ W` tensored with the bra
`⟨δ_m|` (an `(S ∩ W, ∅)`-block map), cast to `LinM D S (S \ W)` along
`(S \ W) ∪ (S ∩ W) = S` and `(S \ W) ∪ ∅ = S \ W`. CoqQ: the family of
`ptraceso_krausso` (`hstensor.v:3282`). -/
noncomputable def ptraceKraus (W : Finset L) (m : QIdx D (S ∩ W)) :
    LinM D S (S \ W) :=
  castF D (sdiff_union_inter S W) (union_empty (S \ W))
    (tenf D (1 : EndM D (S \ W))
      (outerLM (deltav D (default : QIdx D ∅)) (deltav D m)))

/-- The adjoint Kraus operator is the identity tensored with the ket `|δ_m⟩`. -/
theorem adjoint_ptraceKraus (W : Finset L) (m : QIdx D (S ∩ W)) :
    LinearMap.adjoint (ptraceKraus D (S := S) W m)
      = castF D (union_empty (S \ W)) (sdiff_union_inter S W)
          (tenf D (1 : EndM D (S \ W))
            (outerLM (deltav D m) (deltav D (default : QIdx D ∅)))) := by
  rw [ptraceKraus, castF_adj, adjoint_tenf, LinearMap.adjoint_one,
    adjoint_outerLM]

/-- The adjoint Kraus operator sends `δ_l` to `δ` at the merged classical
state: it re-inserts `m` on the traced-out register. -/
theorem adjoint_ptraceKraus_deltav (W : Finset L) (m : QIdx D (S ∩ W))
    (l : QIdx D (S \ W)) :
    LinearMap.adjoint (ptraceKraus D (S := S) W m) (deltav D l)
      = deltav D (QIdx.cast D (sdiff_union_inter S W) (QIdx.merge D l m)) := by
  rw [adjoint_ptraceKraus, castF_apply, castH_deltav, tenf_deltav]
  simp only [QIdx.res_cast, QIdx.res_self, Module.End.one_apply, outerLM_apply,
    dv_dot, if_pos (Subsingleton.elim _ _), one_smul]
  rw [deltav_merge D (disjoint_sdiff_inter S W), castH_deltav]

/-- The Kraus family of the partial trace is a quantum measurement (Q-10
bridge): its completeness relation is the resolution of identity
`∑ m |δ_m⟩⟨δ_m| = 1` on the traced-out factor, lifted by the identity.
The completeness core of CoqQ `ptraceso_qc` (`hstensor.v:3303`). -/
theorem ptraceKraus_isQMeasure (W : Finset L) :
    IsQMeasure D (ptraceKraus D (S := S) W) := by
  unfold IsQMeasure
  have hstep : ∀ m : QIdx D (S ∩ W),
      LinearMap.adjoint (ptraceKraus D (S := S) W m) ∘ₗ ptraceKraus D W m
        = castF D (sdiff_union_inter S W) (sdiff_union_inter S W)
            (tenf D (1 : EndM D (S \ W)) (outerLM (deltav D m) (deltav D m))) := by
    intro m
    rw [adjoint_ptraceKraus, ptraceKraus, ← castF_comp, ← tenf_comp D
      (disjoint_empty_right (S \ W)), one_comp, outerLM_comp, dv_dot,
      if_pos rfl, one_smul]
  rw [Finset.sum_congr rfl fun m _ => hstep m, ← map_sum, ← tenf_sum_right]
  have hres : ∑ m : QIdx D (S ∩ W), outerLM (deltav D m) (deltav D m)
      = (1 : EndM D (S ∩ W)) := by
    simpa only [EuclideanSpace.basisFun_apply, deltav_def] using
      sum_outerLM_self (EuclideanSpace.basisFun (QIdx D (S ∩ W)) ℂ)
  rw [hres, tenf_one_one, castF_one]

/-! ## Q-8: the partial trace -/

/-- **Partial trace over the labels `W`** (Q-8; absent from mathlib). CoqQ
`ptraceso` (`hstensor.v:3259`), here *defined* as the Kraus map of the family
`ptraceKraus` — CoqQ's `ptraceso_krausso` (`hstensor.v:3282`) is then
definitional (`ptraceLM_eq_kraussoOf`), and the concrete matrix-entry model of
spec 04 is the theorem `ptraceLM_deltav_apply`. -/
noncomputable def ptraceLM (W : Finset L) : SuperOp D S (S \ W) :=
  kraussoOf D (ptraceKraus D (S := S) W)

/-- CoqQ `ptraceso_krausso` (`hstensor.v:3282`): the partial trace is the
Kraus map of the bra family `1 ⊗ᶠ ⟨δ_m|`. -/
theorem ptraceLM_eq_kraussoOf (W : Finset L) :
    ptraceLM D (S := S) W = kraussoOf D (ptraceKraus D (S := S) W) := rfl

/-- **M6 acceptance item** — the partial trace is a quantum channel. CoqQ
`ptraceso_qc` (`hstensor.v:3303`). -/
theorem ptraceLM_isQC (W : Finset L) : IsQC D (ptraceLM D (S := S) W) :=
  (isQC_kraussoOf_iff D _).mpr (ptraceKraus_isQMeasure D W)

/-- The partial trace is trace-preserving (the TP half of `ptraceLM_isQC`). -/
theorem ptraceLM_isTP (W : Finset L) : IsTP D (ptraceLM D (S := S) W) :=
  (ptraceLM_isQC D W).2

/-- CoqQ `ptraceso_qc`-corollary: tracing out `W` preserves the full trace. -/
theorem ptrace_trace (W : Finset L) (f : EndM D S) :
    LinearMap.trace ℂ (HS D (S \ W)) (ptraceLM D W f)
      = LinearMap.trace ℂ (HS D S) f :=
  ptraceLM_isTP D W f

/-! ## Q-8: the concrete matrix-entry model (spec 04) -/

/-- The concrete model of spec 04 (Q-8): the matrix entries of the partial
trace sum the entries of `f` over the diagonal of the traced-out register,
`(ptraceLM W f) δ_k` at `l` being `∑ m, f_(merge k m, merge l m)`. Stated for
an arbitrary proof `h : (S \ W) ∪ (S ∩ W) = S` (proof irrelevance). -/
theorem ptraceLM_deltav_apply (W : Finset L) (h : S \ W ∪ S ∩ W = S)
    (f : EndM D S) (k l : QIdx D (S \ W)) :
    ptraceLM D W f (deltav D k) l
      = ∑ m : QIdx D (S ∩ W),
          f (deltav D (QIdx.cast D h (QIdx.merge D k m)))
            (QIdx.cast D h (QIdx.merge D l m)) := by
  rw [← inner_deltav D l, ptraceLM_eq_kraussoOf, kraussoOf_apply]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, inner_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← LinearMap.adjoint_inner_left (ptraceKraus D W m),
    adjoint_ptraceKraus_deltav, adjoint_ptraceKraus_deltav, inner_deltav]

/-- The partial trace of the identity is the dimension of the traced-out
factor times the identity (CoqQ `ptraceso`-suite computation). -/
theorem ptraceLM_one (W : Finset L) :
    ptraceLM D W (1 : EndM D S)
      = (Fintype.card (QIdx D (S ∩ W)) : ℂ) • 1 := by
  refine linM_ext D fun k => PiLp.ext fun l => ?_
  rw [ptraceLM_deltav_apply D W (sdiff_union_inter S W)]
  have hmerge : ∀ m : QIdx D (S ∩ W),
      (QIdx.cast D (sdiff_union_inter S W) (QIdx.merge D l m)
          = QIdx.cast D (sdiff_union_inter S W) (QIdx.merge D k m)) ↔ l = k := by
    intro m
    rw [(QIdx.cast D (sdiff_union_inter S W)).injective.eq_iff]
    constructor
    · intro hkl
      have := congrArg (QIdx.res D subset_union_left) hkl
      simpa only [QIdx.res_merge_left] using this
    · rintro rfl; rfl
  simp only [Module.End.one_apply, deltav_apply, hmerge, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_ite, mul_one, mul_zero,
    LinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul]

end Qhl
