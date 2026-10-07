import Qhl.History.SeqDecomp

/-!
# L-1: assertions, predicate transformers, and the two judgements

Subgoal L-1 of spec 07 (paper arXiv:2412.09869 Def 4.7–4.8, Def 5.1).

Decision **V1**: an assertion is a bundled *family of effects*
`op : σT → EndM D univ`, the semantic rendering of the paper's syntactic pair
`(φ, A)`. The classical formula `φ` becomes a **mask**: `Assn.mask A φ` is `A`
where `φ` holds and `0` elsewhere, which is exactly what Def 5.1's filtered
sum does with terminal states violating the postcondition's classical part.
`mask`/`mand`/`mandNot`/`guard` recover every rule shape of Tables 2–3 (L-3).

Decision **V2**: the predicate transformers of the atomic axioms are given
*concretely* here — `A ∘ f`, `E†(A)`, `U†AU`, `Σᵢ Mᵢ†A(updᵢσ)Mᵢ` — and each
comes with an `expect` law which is an **equality** (§2.6 of spec 07), so the
atomic soundness proofs are computations, not estimates.

Decision **V7**: the paper leaves `σ(A)` *undefined* where a `Dist` side
condition fails. Assertions here are total, so `unitaryPre`/`measurePre`
return `0` on that branch; since `stepProg` produces no successor there, the
triple holds for the same reason it does in the paper (`PostH = 0`,
`NT = mass`).
-/

namespace Qhl

open Finset
open scoped NNReal ENNReal ComplexOrder

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## Effect-closure helpers -/

section EffectClosure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Conjugation is monotone for the Löwner order (`K†(B−A)K` is positive). -/
theorem conj_le_conj {A B : E →ₗ[ℂ] E} (K : E →ₗ[ℂ] E) (h : A ≤ B) :
    LinearMap.adjoint K ∘ₗ A ∘ₗ K ≤ LinearMap.adjoint K ∘ₗ B ∘ₗ K := by
  rw [LinearMap.le_def] at h ⊢
  rw [show LinearMap.adjoint K ∘ₗ B ∘ₗ K - LinearMap.adjoint K ∘ₗ A ∘ₗ K
      = LinearMap.adjoint K ∘ₗ (B - A) ∘ₗ K by
    simp only [LinearMap.comp_sub, LinearMap.sub_comp]]
  exact h.adjoint_conj K

/-- L-1: `K†AK` is an effect whenever `A` is and `K†K ≤ 1` (covers the
unitary case, where `K†K = 1`). -/
theorem isEffect_conj {A K : E →ₗ[ℂ] E} (hA : IsEffect A)
    (h1 : LinearMap.adjoint K ∘ₗ K ≤ 1) : IsEffect (LinearMap.adjoint K ∘ₗ A ∘ₗ K) := by
  refine ⟨(LinearMap.nonneg_iff_isPositive _).mpr (hA.isPositive.adjoint_conj K), ?_⟩
  refine le_trans (conj_le_conj K hA.2) (le_trans (le_of_eq ?_) h1)
  rw [Module.End.one_eq_id, LinearMap.id_comp]

/-- L-1: the measurement form `Σᵢ Kᵢ†AᵢKᵢ` is an effect whenever each `Aᵢ` is
and the family satisfies the completeness relation. -/
theorem isEffect_sum_conj {ι : Type*} [Fintype ι] {A K : ι → E →ₗ[ℂ] E}
    (hA : ∀ i, IsEffect (A i)) (h1 : ∑ i, LinearMap.adjoint (K i) ∘ₗ K i = 1) :
    IsEffect (∑ i, LinearMap.adjoint (K i) ∘ₗ A i ∘ₗ K i) := by
  refine ⟨(LinearMap.nonneg_iff_isPositive _).mpr
      (LinearMap.isPositive_sum _ fun i _ => (hA i).isPositive.adjoint_conj (K i)), ?_⟩
  have hone : ∑ i, LinearMap.adjoint (K i) ∘ₗ (1 : E →ₗ[ℂ] E) ∘ₗ K i
      = ∑ i, LinearMap.adjoint (K i) ∘ₗ K i :=
    Finset.sum_congr rfl fun i _ => by rw [Module.End.one_eq_id, LinearMap.id_comp]
  exact le_trans (Finset.sum_le_sum fun i _ => conj_le_conj (K i) (hA i).2)
    (le_of_eq (hone.trans h1))

end EffectClosure

/-! ## The dual of the initialisation channel preserves effects -/

/-- The initialisation channel of a cell set, in Kraus form on the whole
world. -/
theorem initLift_eq_kraussoOf (S : Finset L) :
    initLift (D := D) S = kraussoOf D fun x : QIdx D S =>
      liftF D (subset_univ S) (outerLM (deltav D (default : QIdx D S)) (deltav D x)) := by
  rw [initLift, initSO, liftSO_kraussoOf]

theorem dualSO_initLift_isPositive {S : Finset L} {A : EndM D (univ : Finset L)}
    (hA : A.IsPositive) : (dualSO D (initLift (D := D) S) A).IsPositive := by
  rw [initLift_eq_kraussoOf, dualSO_kraussoOf]
  exact kraussoOf_isPositive D _ hA

theorem dualSO_initLift_mono {S : Finset L} {A B : EndM D (univ : Finset L)}
    (h : A ≤ B) : dualSO D (initLift (D := D) S) A ≤ dualSO D (initLift (D := D) S) B := by
  rw [LinearMap.le_def] at h ⊢
  rw [← map_sub]
  exact dualSO_initLift_isPositive h

/-- `E†` maps effects to effects: positivity is the Kraus form, and
`E†(A) ≤ E†(1) = 1` because `E` is trace-preserving. -/
theorem isEffect_dualSO_initLift {S : Finset L} {A : EndM D (univ : Finset L)}
    (hA : IsEffect A) : IsEffect (dualSO D (initLift (D := D) S) A) :=
  ⟨(LinearMap.nonneg_iff_isPositive _).mpr (dualSO_initLift_isPositive hA.isPositive),
    le_of_le_of_eq (dualSO_initLift_mono hA.2)
      (IsTP.isUnital_dualSO D (initLift_isQC (D := D) S).2)⟩

/-! ## L-1: assertions -/

/-- L-1 (V1): an assertion is a family of effects on the whole world indexed
by the classical state. The paper's classical component is recovered as a
mask (`Assn.mask`). -/
structure Assn (σT : Type*) {L : Type*} [Fintype L] [DecidableEq L]
    (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] where
  /-- The effect attached to each classical state. -/
  op : σT → EndM D (univ : Finset L)
  /-- Every member of the family is an effect. -/
  isEffect : ∀ σ, IsEffect (op σ)

namespace Assn

@[ext]
theorem ext {A B : Assn σT D} (h : A.op = B.op) : A = B := by
  cases A; cases B; simpa using h

theorem isPositive (A : Assn σT D) (σ : σT) : (A.op σ).IsPositive := (A.isEffect σ).isPositive

/-- Pointwise Löwner order on assertions (the quantum half of the paper's
cq-entailment, Def 4.8). -/
instance : LE (Assn σT D) := ⟨fun A B => ∀ σ, A.op σ ≤ B.op σ⟩

theorem le_def {A B : Assn σT D} : A ≤ B ↔ ∀ σ, A.op σ ≤ B.op σ := Iff.rfl

theorem le_refl' (A : Assn σT D) : A ≤ A := fun _ => le_rfl

/-- Anything is below `1`: the useful shape when a precondition's mask is
open and the transformer collapses to the identity effect. -/
theorem le_op_of_eq_one {A B : Assn σT D} {σ : σT} (h : B.op σ = 1) :
    A.op σ ≤ B.op σ := h ▸ (A.isEffect σ).2

/-- `0` is below anything: the useful shape when a precondition's mask is
closed. -/
theorem op_zero_le {A B : Assn σT D} {σ : σT} (h : A.op σ = 0) :
    A.op σ ≤ B.op σ := h ▸ (B.isEffect σ).1

theorem le_trans' {A B C : Assn σT D} (hAB : A ≤ B) (hBC : B ≤ C) : A ≤ C :=
  fun σ => (hAB σ).trans (hBC σ)

/-- The everywhere-false assertion. -/
def zero : Assn σT D := ⟨fun _ => 0, fun _ => isEffect_zero⟩

/-- The everywhere-true assertion (the paper's `1`). -/
def one : Assn σT D := ⟨fun _ => 1, fun _ => isEffect_one⟩

@[simp] theorem zero_op (σ : σT) : (zero : Assn σT D).op σ = 0 := rfl
@[simp] theorem one_op (σ : σT) : (one : Assn σT D).op σ = 1 := rfl

/-! ### Combinators -/

/-- Substitution: precompose the family with a classical state map. -/
def comp (A : Assn σT D) (f : σT → σT) : Assn σT D :=
  ⟨fun σ => A.op (f σ), fun σ => A.isEffect (f σ)⟩

@[simp] theorem comp_op (A : Assn σT D) (f : σT → σT) (σ : σT) :
    (A.comp f).op σ = A.op (f σ) := rfl

/-- V1: the classical component of the paper's pair, as a mask. `Classical`
decidability keeps the definition free of instance noise (it is already
noncomputable). -/
noncomputable def mask (A : Assn σT D) (φ : σT → Prop) : Assn σT D where
  op σ := @ite _ (φ σ) (Classical.propDecidable _) (A.op σ) 0
  isEffect σ := by
    by_cases h : φ σ
    · rw [if_pos h]; exact A.isEffect σ
    · rw [if_neg h]; exact isEffect_zero

@[simp]
theorem mask_op_of_pos {A : Assn σT D} {φ : σT → Prop} {σ : σT} (h : φ σ) :
    (A.mask φ).op σ = A.op σ := if_pos h

@[simp]
theorem mask_op_of_neg {A : Assn σT D} {φ : σT → Prop} {σ : σT} (h : ¬ φ σ) :
    (A.mask φ).op σ = 0 := if_neg h

/-- Masking with a Boolean guard (the paper's `φ ∧ b`). -/
noncomputable def mand (A : Assn σT D) (b : σT → Bool) : Assn σT D :=
  A.mask fun σ => b σ = true

/-- Masking with a negated Boolean guard (the paper's `φ ∧ ¬b`). -/
noncomputable def mandNot (A : Assn σT D) (b : σT → Bool) : Assn σT D :=
  A.mask fun σ => b σ = false

@[simp]
theorem mand_op_of_true {A : Assn σT D} {b : σT → Bool} {σ : σT} (h : b σ = true) :
    (A.mand b).op σ = A.op σ := mask_op_of_pos h

@[simp]
theorem mand_op_of_false {A : Assn σT D} {b : σT → Bool} {σ : σT} (h : b σ = false) :
    (A.mand b).op σ = 0 := mask_op_of_neg (by simp [h])

@[simp]
theorem mandNot_op_of_false {A : Assn σT D} {b : σT → Bool} {σ : σT} (h : b σ = false) :
    (A.mandNot b).op σ = A.op σ := mask_op_of_pos h

@[simp]
theorem mandNot_op_of_true {A : Assn σT D} {b : σT → Bool} {σ : σT} (h : b σ = true) :
    (A.mandNot b).op σ = 0 := mask_op_of_neg (by simp [h])

/-- The branching combinator behind (R-Cond); strictly more general than the
paper's rule, which is the instance `guard_mask_guard` of L-3. -/
def guard (b : σT → Bool) (A₁ A₀ : Assn σT D) : Assn σT D where
  op σ := if b σ then A₁.op σ else A₀.op σ
  isEffect σ := by
    by_cases h : b σ = true
    · rw [if_pos h]; exact A₁.isEffect σ
    · rw [if_neg h]; exact A₀.isEffect σ

@[simp]
theorem guard_op_of_true {b : σT → Bool} {A₁ A₀ : Assn σT D} {σ : σT} (h : b σ = true) :
    (guard b A₁ A₀).op σ = A₁.op σ := if_pos h

@[simp]
theorem guard_op_of_false {b : σT → Bool} {A₁ A₀ : Assn σT D} {σ : σT} (h : b σ = false) :
    (guard b A₁ A₀).op σ = A₀.op σ := if_neg (by simp [h])

/-! ### V2: the predicate transformers of the atomic axioms -/

/-- (Ax-Init): `E†(A)` for the initialisation channel of `S σ`. -/
noncomputable def initPre (A : Assn σT D) (S : σT → Finset L) : Assn σT D where
  op σ := dualSO D (initLift (S σ)) (A.op σ)
  isEffect σ := isEffect_dualSO_initLift (A.isEffect σ)

@[simp]
theorem initPre_op (A : Assn σT D) (S : σT → Finset L) (σ : σT) :
    (A.initPre S).op σ = dualSO D (initLift (S σ)) (A.op σ) := rfl

/-- The initialisation transformer of `1` is `1` — the dual of a channel is
unital (`IsTP.isUnital_dualSO`). -/
theorem initPre_one_op (S : σT → Finset L) (σ : σT) :
    ((one : Assn σT D).initPre S).op σ = 1 :=
  IsTP.isUnital_dualSO D (initLift_isQC (S σ)).2

/-- (Ax-Uni): `U†AU` on the evaluated register; `0` where `Dist` fails (V7). -/
noncomputable def unitaryPre (A : Assn σT D) {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) : Assn σT D where
  op σ := if h : Function.Injective (r σ) then
      LinearMap.adjoint (regLift ⟨r σ, h⟩ (U σ)) ∘ₗ A.op σ ∘ₗ regLift ⟨r σ, h⟩ (U σ)
    else 0
  isEffect σ := by
    by_cases h : Function.Injective (r σ)
    · rw [dif_pos h]
      refine isEffect_conj (A.isEffect σ) (le_of_eq ?_)
      rw [(isUnitary_regLift ⟨r σ, h⟩ (U σ)).1]
    · rw [dif_neg h]; exact isEffect_zero

theorem unitaryPre_op_of_dist (A : Assn σT D) {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) {σ : σT} (h : Function.Injective (r σ)) :
    (A.unitaryPre r U).op σ
      = LinearMap.adjoint (regLift ⟨r σ, h⟩ (U σ)) ∘ₗ A.op σ ∘ₗ regLift ⟨r σ, h⟩ (U σ) :=
  dif_pos h

theorem unitaryPre_op_of_not_dist (A : Assn σT D) {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) {σ : σT} (h : ¬ Function.Injective (r σ)) :
    (A.unitaryPre r U).op σ = 0 :=
  dif_neg h

/-- The unitary transformer of `1` is `1` — this *is* the unitarity relation
`U†U = 1` carried by the bundled gate (Decision W5). -/
theorem unitaryPre_one_op {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) {σ : σT} (h : Function.Injective (r σ)) :
    ((one : Assn σT D).unitaryPre r U).op σ = 1 := by
  rw [unitaryPre_op_of_dist _ r U h, one_op, Module.End.one_eq_id, LinearMap.id_comp]
  exact (isUnitary_regLift ⟨r σ, h⟩ (U σ)).1

/-- If a register expression is well formed in every classical state, the
unitary transformer fixes `1`. -/
theorem unitaryPre_one {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (h : ∀ σ, Function.Injective (r σ)) :
    (one : Assn σT D).unitaryPre r U = one :=
  ext (funext fun σ => unitaryPre_one_op r U (h σ))

/-- (Ax-Meas) in Born-sum transformer form (V3): `Σᵢ Mᵢ† A(updᵢ σ) Mᵢ`,
`0` where `Dist` fails (V7). The paper's ghost variable `y` exists only to
avoid a `Σ` in the *syntax*; semantically this sum is the exact transformer. -/
noncomputable def measurePre (A : Assn σT D) {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ))) (upd : Fin m → σT → σT) : Assn σT D where
  op σ := if h : Function.Injective (r σ) then
      ∑ i, LinearMap.adjoint (regLift ⟨r σ, h⟩ ((M σ).M i)) ∘ₗ A.op (upd i σ)
        ∘ₗ regLift ⟨r σ, h⟩ ((M σ).M i)
    else 0
  isEffect σ := by
    by_cases h : Function.Injective (r σ)
    · rw [dif_pos h]
      exact isEffect_sum_conj (fun i => A.isEffect (upd i σ))
        (isQMeasure_regLift ⟨r σ, h⟩ (M σ))
    · rw [dif_neg h]; exact isEffect_zero

theorem measurePre_op_of_dist (A : Assn σT D) {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ))) (upd : Fin m → σT → σT) {σ : σT}
    (h : Function.Injective (r σ)) :
    (A.measurePre r M upd).op σ
      = ∑ i, LinearMap.adjoint (regLift ⟨r σ, h⟩ ((M σ).M i)) ∘ₗ A.op (upd i σ)
          ∘ₗ regLift ⟨r σ, h⟩ ((M σ).M i) :=
  dif_pos h

theorem measurePre_op_of_not_dist (A : Assn σT D) {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ))) (upd : Fin m → σT → σT) {σ : σT}
    (h : ¬ Function.Injective (r σ)) :
    (A.measurePre r M upd).op σ = 0 :=
  dif_neg h

/-- The measurement transformer of `1` is `1` — this *is* the completeness
relation `Σᵢ Mᵢ†Mᵢ = 1` carried by the bundled `QMeasure` (Decision W5). -/
theorem measurePre_one_op {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ))) (upd : Fin m → σT → σT) {σ : σT}
    (h : Function.Injective (r σ)) :
    ((one : Assn σT D).measurePre r M upd).op σ = 1 := by
  rw [measurePre_op_of_dist _ r M upd h,
    show (∑ i, LinearMap.adjoint (regLift ⟨r σ, h⟩ ((M σ).M i))
          ∘ₗ (one : Assn σT D).op (upd i σ) ∘ₗ regLift ⟨r σ, h⟩ ((M σ).M i))
        = ∑ i, LinearMap.adjoint (regLift ⟨r σ, h⟩ ((M σ).M i))
            ∘ₗ regLift ⟨r σ, h⟩ ((M σ).M i) from
      Finset.sum_congr rfl fun i _ => by
        rw [one_op, Module.End.one_eq_id, LinearMap.id_comp]]
  exact isQMeasure_regLift ⟨r σ, h⟩ (M σ)

end Assn

/-! ## §2.6: the expectation algebra (all equalities) -/

private theorem comp_sum_endM {ι : Type*} (s : Finset ι) (g : EndM D (univ : Finset L))
    (f : ι → EndM D (univ : Finset L)) : g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, LinearMap.comp_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, LinearMap.comp_add, ih]

theorem expect_comp (B : σT → EndM D (univ : Finset L)) (f : σT → σT) (s : CQState σT D) :
    expect (fun σ => B (f σ)) s = expect B ⟨f s.cls, s.q⟩ := rfl

/-- Trace cyclicity: conjugating the assertion is conjugating the state. -/
theorem expect_conj (B : σT → EndM D (univ : Finset L)) (K : EndM D (univ : Finset L))
    (σ' : σT) (s : CQState σT D) :
    expect (fun _ => LinearMap.adjoint K ∘ₗ B σ' ∘ₗ K) s = expect B ⟨σ', s.q.conj K⟩ := by
  rw [expect, expect]
  congr 1
  rw [show s.q.op ∘ₗ (LinearMap.adjoint K ∘ₗ B σ' ∘ₗ K)
      = ((s.q.op ∘ₗ LinearMap.adjoint K) ∘ₗ B σ') ∘ₗ K by
    simp only [LinearMap.comp_assoc], LinearMap.trace_comp_comm' K]
  change LinearMap.trace ℂ (HS D (univ : Finset L))
      (K ∘ₗ ((s.q.op ∘ₗ LinearMap.adjoint K) ∘ₗ B σ')) = _
  congr 1

/-- The defining property of `dualSO`, at the level of expectations. -/
theorem expect_dualSO (B : σT → EndM D (univ : Finset L))
    (E : SuperOp D (univ : Finset L) (univ : Finset L)) (hE : IsCP D E)
    (s : CQState σT D) :
    expect (fun σ => dualSO D E (B σ)) s = expect B ⟨s.cls, s.q.mapSO E hE⟩ := by
  rw [expect, expect, trace_comp_dualSO]
  rfl

/-- The Born sum: the measurement transformer distributes over the branches. -/
theorem expect_sum_conj {m : ℕ} (B : σT → EndM D (univ : Finset L))
    (K : Fin m → EndM D (univ : Finset L)) (upd : Fin m → σT → σT) (s : CQState σT D) :
    expect (fun σ => ∑ i, LinearMap.adjoint (K i) ∘ₗ B (upd i σ) ∘ₗ K i) s
      = ∑ i, expect B ⟨upd i s.cls, s.q.conj (K i)⟩ := by
  rw [expect, comp_sum_endM, map_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => expect_conj B (K i) (upd i s.cls) s

/-! ## `expectE` of the combinators -/

@[simp]
theorem expectE_mask_of_pos {A : Assn σT D} {φ : σT → Prop} {s : CQState σT D}
    (h : φ s.cls) : expectE (A.mask φ).op s = expectE A.op s := by
  simp only [expectE, expect, Assn.mask_op_of_pos h]

@[simp]
theorem expectE_mask_of_neg {A : Assn σT D} {φ : σT → Prop} {s : CQState σT D}
    (h : ¬ φ s.cls) : expectE (A.mask φ).op s = 0 := by
  simp only [expectE, expect, Assn.mask_op_of_neg h, LinearMap.comp_zero, map_zero,
    Complex.zero_re, ENNReal.ofReal_zero]

@[simp]
theorem expectE_mand_of_true {A : Assn σT D} {b : σT → Bool} {s : CQState σT D}
    (h : b s.cls = true) : expectE (A.mand b).op s = expectE A.op s :=
  expectE_mask_of_pos h

@[simp]
theorem expectE_mand_of_false {A : Assn σT D} {b : σT → Bool} {s : CQState σT D}
    (h : b s.cls = false) : expectE (A.mand b).op s = 0 :=
  expectE_mask_of_neg (by simp [h])

@[simp]
theorem expectE_mandNot_of_false {A : Assn σT D} {b : σT → Bool} {s : CQState σT D}
    (h : b s.cls = false) : expectE (A.mandNot b).op s = expectE A.op s :=
  expectE_mask_of_pos h

@[simp]
theorem expectE_mandNot_of_true {A : Assn σT D} {b : σT → Bool} {s : CQState σT D}
    (h : b s.cls = true) : expectE (A.mandNot b).op s = 0 :=
  expectE_mask_of_neg (by simp [h])

@[simp]
theorem expectE_guard_of_true {b : σT → Bool} {A₁ A₀ : Assn σT D} {s : CQState σT D}
    (h : b s.cls = true) : expectE (Assn.guard b A₁ A₀).op s = expectE A₁.op s := by
  simp only [expectE, expect, Assn.guard_op_of_true h]

@[simp]
theorem expectE_guard_of_false {b : σT → Bool} {A₁ A₀ : Assn σT D} {s : CQState σT D}
    (h : b s.cls = false) : expectE (Assn.guard b A₁ A₀).op s = expectE A₀.op s := by
  simp only [expectE, expect, Assn.guard_op_of_false h]

theorem expectE_le_mass' (A : Assn σT D) (s : CQState σT D) :
    expectE A.op s ≤ ((s.q.mass : ℝ≥0) : ℝ≥0∞) :=
  expectE_le_mass A.isEffect s

/-- The expectation of the assertion `1` is the mass of the state. This is
what turns a triple `{1} P {1}` into a statement about *all* the mass. -/
theorem expectE_one (s : CQState σT D) :
    expectE (Assn.one : Assn σT D).op s = ((s.q.mass : ℝ≥0) : ℝ≥0∞) := by
  rw [expectE, expect]
  simp only [Assn.one_op, Module.End.one_eq_id, LinearMap.comp_id]
  rw [← PDensity.coe_mass, ENNReal.ofReal_coe_nnreal]

/-! ## L-1: the two judgements (spec 07 §2, paper (15)/(16)) -/

/-- Total correctness of a triple of assertion families (paper (15)). -/
def validTot (A : Assn σT D) (P : Prog σT D) (B : Assn σT D) : Prop :=
  ∀ s : CQState σT D, expectE A.op s ≤ PostH (Config.init P s) B.op

/-- Partial correctness of a triple of assertion families (paper (16)). -/
def validPar (A : Assn σT D) (P : Prog σT D) (B : Assn σT D) : Prop :=
  ∀ s : CQState σT D,
    expectE A.op s ≤ PostH (Config.init P s) B.op + NT (Config.init P s)

theorem validTot.validPar {A B : Assn σT D} {P : Prog σT D} (h : validTot A P B) :
    validPar A P B := fun s => (h s).trans le_self_add

/-- L-1 (K1 + K2): partial correctness is exactly a statement about the
bounded value functional at every depth — the step-indexed rendering of the
paper's Claim (37). This is what makes the `while` rule provable by strong
induction on the step depth (V4). -/
theorem validPar_iff_forall_le_Val {A B : Assn σT D} {P : Prog σT D} :
    validPar A P B ↔ ∀ (s : CQState σT D) (N : ℕ),
      expectE A.op s ≤ Val (Config.init P s) N B.op := by
  constructor
  · intro h s N
    exact (h s).trans (PostH_add_NT_le_Val B.isEffect _ N)
  · intro h s
    exact le_PostH_add_NT_of_forall_le_Val (fun σ => B.isPositive σ) (h s)

end Qhl
