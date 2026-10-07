import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Foundations: outer products, conjugation, transpose, operator predicates

Mirror of the parts of `CoqQ/src/hermitian.v` and `quantum.v` needed by the
Dirac layer (spec 01, subgoals F-1..F-4 and F-L3/F-L4).

* `outerLM u v` — the outer product `|u⟩⟨v|` as a plain linear map (CoqQ `outp`)
* `conjV` — pointwise conjugation on `EuclideanSpace ℂ ι` (CoqQ `conjv`)
* `conjLM f`, `transposeLM f` — basis conjugate `f^C` and transpose `f^T`
  (CoqQ `conj_lfun`, `tr_lfun`), with the adjoint/conjugate/transpose lattice
* `IsEffect`, `IsDensity`, `IsDensity1`, `IsProjOp`, `IsIsometryOp` — operator
  predicates (CoqQ `obslf`, `denlf`, `den1lf`, `projlf`, `isolf`)

F-5 check (spec 01 §3): this mathlib **does** provide a `Star (E →ₗ[𝕜] E)`
instance via the adjoint in finite dimension: `Mathlib/Analysis/InnerProductSpace/
Adjoint.lean` declares (in the `[FiniteDimensional 𝕜 E]` section) `Star`,
`InvolutiveStar`, `StarMul`, `StarRing` and `StarModule 𝕜` instances on
`E →ₗ[𝕜] E` (auto-named `LinearMap.instStarId`, `LinearMap.instStarRingId`,
`LinearMap.instStarModuleId`, ...) with `star = adjoint`
(`LinearMap.star_eq_adjoint`). We do not add any instance here.
-/

namespace Qhl

open scoped ComplexInnerProductSpace

/-! ## F-1: the outer product `|u⟩⟨v|` -/

section OuterLM

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- The outer product `|u⟩⟨v| : w ↦ ⟪v, w⟫ • u` as a plain linear map.
CoqQ: `outp` (`hermitian.v:614,829`). Definitionally equal to mathlib's
continuous-bundled `InnerProductSpace.rankOne`; see `outerLM_eq_rankOne`. -/
noncomputable def outerLM (u : E) (v : F) : F →ₗ[ℂ] E :=
  (innerₛₗ ℂ v).smulRight u

@[simp]
theorem outerLM_apply (u : E) (v w : F) : outerLM u v w = ⟪v, w⟫ • u := rfl

/-- Link to mathlib's continuous-linear-map bundle. -/
theorem outerLM_eq_rankOne (u : E) (v : F) :
    outerLM u v = (InnerProductSpace.rankOne ℂ u v).toLinearMap := rfl

/-- CoqQ `outp_comp` (`hermitian.v:1135`): `|u⟩⟨v| ∘ |w⟩⟨t| = ⟪v,w⟫ • |u⟩⟨t|`. -/
theorem outerLM_comp (u : E) (v w : F) (t : G) :
    outerLM u v ∘ₗ outerLM w t = ⟪v, w⟫ • outerLM u t := by
  refine LinearMap.ext fun x => ?_
  simp [smul_smul, mul_comm]

/-- CoqQ `adj_outp` (`hermitian.v:1140`): `(|u⟩⟨v|)† = |v⟩⟨u|`. -/
@[simp]
theorem adjoint_outerLM [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (u : E) (v : F) :
    LinearMap.adjoint (outerLM u v) = outerLM v u := by
  refine ((LinearMap.eq_adjoint_iff _ _).mpr fun x y => ?_).symm
  simp only [outerLM_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
  exact mul_comm _ _

/-- Additivity in the ket slot. CoqQ `outp_addl`. -/
theorem outerLM_add_left (u u' : E) (v : F) :
    outerLM (u + u') v = outerLM u v + outerLM u' v :=
  LinearMap.ext fun w => by
    simp only [outerLM_apply, LinearMap.add_apply, smul_add]

/-- Additivity in the bra slot. CoqQ `outp_addr`. -/
theorem outerLM_add_right (u : E) (v v' : F) :
    outerLM u (v + v') = outerLM u v + outerLM u v' :=
  LinearMap.ext fun w => by
    simp only [outerLM_apply, LinearMap.add_apply, inner_add_left, add_smul]

/-- Linearity in the ket slot. CoqQ `outp_scalel`. -/
theorem outerLM_smul_left (c : ℂ) (u : E) (v : F) :
    outerLM (c • u) v = c • outerLM u v :=
  LinearMap.ext fun w => by
    simp only [outerLM_apply, LinearMap.smul_apply, smul_smul, mul_comm]

/-- Conjugate-linearity in the bra slot. CoqQ `outp_scaler`. -/
theorem outerLM_smul_right (c : ℂ) (u : E) (v : F) :
    outerLM u (c • v) = star c • outerLM u v :=
  LinearMap.ext fun w => by
    simp only [outerLM_apply, LinearMap.smul_apply, inner_smul_left, mul_smul,
      RCLike.star_def]

/-- F-L3, CoqQ `outp_trlf` (`hermitian.v:1155`): `Tr |u⟩⟨v| = ⟪v, u⟫`. -/
@[simp]
theorem trace_outerLM [FiniteDimensional ℂ E] (u v : E) :
    LinearMap.trace ℂ E (outerLM u v) = ⟪v, u⟫ := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E)]
  simp only [outerLM_apply, inner_smul_right]
  exact (stdOrthonormalBasis ℂ E).sum_inner_mul_inner v u

/-- Resolution of the identity: for an orthonormal basis `b`,
`∑ i, |b i⟩⟨b i| = 1`. Layer-0 core of CoqQ `sumonb_outerM` (`dirac.v:2256`). -/
theorem sum_outerLM_self {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) :
    ∑ i, outerLM (b i) (b i) = (1 : E →ₗ[ℂ] E) :=
  LinearMap.ext fun x => by
    simp only [LinearMap.sum_apply, outerLM_apply, Module.End.one_apply]
    exact b.sum_repr' x

/-- `x ∘ |u⟩⟨v| = |x u⟩⟨v|`. Spec 04 support (Q-5/Q-6). -/
theorem comp_outerLM (x : E →ₗ[ℂ] G) (u : E) (v : F) :
    x ∘ₗ outerLM u v = outerLM (x u) v :=
  LinearMap.ext fun w => by simp

/-- `Tr (x ∘ |u⟩⟨v|) = ⟪v, x u⟫`. Spec 04 support (Q-5/Q-6). -/
theorem trace_comp_outerLM [FiniteDimensional ℂ F] (x : E →ₗ[ℂ] F) (u : E) (v : F) :
    LinearMap.trace ℂ F (x ∘ₗ outerLM u v) = ⟪v, x u⟫ := by
  rw [comp_outerLM, trace_outerLM]

/-- `Tr (|u⟩⟨v| ∘ x) = ⟪v, x u⟫` — trace cyclicity on rank-ones.
Spec 04 support (Q-5/Q-6). -/
theorem trace_outerLM_comp [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (u : E) (v : F) (x : E →ₗ[ℂ] F) :
    LinearMap.trace ℂ E (outerLM u v ∘ₗ x) = ⟪v, x u⟫ := by
  rw [LinearMap.trace_comp_comm', trace_comp_outerLM]

/-- Additivity of the outer product in the ket over finite sums. -/
theorem outerLM_sum_left {α : Type*} (s : Finset α) (u : α → E) (v : F) :
    outerLM (∑ a ∈ s, u a) v = ∑ a ∈ s, outerLM (u a) v :=
  LinearMap.ext fun w => by simp [Finset.smul_sum]

/-- Column decomposition over an orthonormal basis: `x = ∑ i, |x (b i)⟩⟨b i|`.
Spec 04 support (Q-6; also feeds the Choi machinery of Q-4). -/
theorem eq_sum_outerLM {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E)
    (x : E →ₗ[ℂ] F) : x = ∑ i, outerLM (x (b i)) (b i) := by
  refine LinearMap.ext fun w => ?_
  conv_lhs => rw [← b.sum_repr' w]
  rw [map_sum]
  simp only [LinearMap.sum_apply, outerLM_apply, map_smul]

/-- Linear maps out of an operator space agreeing on all basis outer products
`|c j⟩⟨b i|` are equal — the `ext` workhorse for super-operator arguments
(spec 04, Q-6/Q-7). -/
theorem outerLM_ext {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ F)
    {W : Type*} [AddCommMonoid W] [Module ℂ W] {Φ Ψ : (E →ₗ[ℂ] F) →ₗ[ℂ] W}
    (h : ∀ (j : κ) (i : ι), Φ (outerLM (c j) (b i)) = Ψ (outerLM (c j) (b i))) :
    Φ = Ψ := by
  refine LinearMap.ext fun x => ?_
  rw [eq_sum_outerLM b x, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : outerLM (x (b i)) (b i) = ∑ j, ⟪c j, x (b i)⟫ • outerLM (c j) (b i) := by
    conv_lhs => rw [← c.sum_repr' (x (b i)), outerLM_sum_left]
    exact Finset.sum_congr rfl fun j _ => outerLM_smul_left _ _ _
  rw [hx, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul, h]

end OuterLM

/-! ## F-2: conjugation of vectors relative to the canonical basis -/

section ConjV

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

/-- Componentwise conjugation on `EuclideanSpace ℂ ι` (relative to the
canonical basis). CoqQ: `conjv` (`hermitian.v:611`). -/
def conjV (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (star v.ofLp)

@[simp]
theorem conjV_apply (v : EuclideanSpace ℂ ι) (i : ι) : conjV v i = star (v i) := rfl

/-- CoqQ `conjvK`: conjugation is involutive. -/
@[simp]
theorem conjV_conjV (v : EuclideanSpace ℂ ι) : conjV (conjV v) = v := by
  ext i
  simp

theorem conjV_add (u v : EuclideanSpace ℂ ι) : conjV (u + v) = conjV u + conjV v := by
  ext i
  simp

/-- Conjugate-linearity of `conjV`. CoqQ `conjv_scale`. -/
theorem conjV_smul (c : ℂ) (v : EuclideanSpace ℂ ι) :
    conjV (c • v) = star c • conjV v := by
  ext i
  simp

/-- `conjV` on the canonical basis vectors. -/
@[simp]
theorem conjV_single [DecidableEq ι] (i : ι) (c : ℂ) :
    conjV (EuclideanSpace.single i c) = EuclideanSpace.single i (star c) := by
  ext j
  rw [conjV_apply, PiLp.single_apply, PiLp.single_apply, apply_ite (star : ℂ → ℂ), star_zero]

/-- CoqQ `conjv_cb`: the canonical basis is fixed by conjugation. -/
theorem conjV_basisFun [DecidableEq ι] (i : ι) :
    conjV (EuclideanSpace.basisFun ι ℂ i) = EuclideanSpace.basisFun ι ℂ i := by
  simp [EuclideanSpace.basisFun_apply]

/-- CoqQ `conjv_dot` (`hermitian.v:1050`): `⟪u^*, v^*⟫ = ⟪v, u⟫`. -/
theorem inner_conjV (u v : EuclideanSpace ℂ ι) : ⟪conjV u, conjV v⟫ = ⟪v, u⟫ := by
  simp [PiLp.inner_apply, RCLike.inner_apply, RCLike.star_def, mul_comm]

/-- CoqQ `conjv_dotl`: `⟪u^*, v⟫ = ⟪v^*, u⟫` (the bilinear pairing is symmetric). -/
theorem inner_conjV_left (u v : EuclideanSpace ℂ ι) : ⟪conjV u, v⟫ = ⟪conjV v, u⟫ := by
  simp [PiLp.inner_apply, RCLike.inner_apply, RCLike.star_def, mul_comm]

/-- CoqQ `conjv_dotr`: `⟪u, v^*⟫ = ⟪v, u^*⟫`. -/
theorem inner_conjV_right (u v : EuclideanSpace ℂ ι) : ⟪u, conjV v⟫ = ⟪v, conjV u⟫ := by
  rw [← inner_conj_symm, inner_conjV_left, inner_conj_symm]

/-! ## F-3: conjugation and transposition of linear maps; the A/C/T lattice

`adjoint` (A) is mathlib's `LinearMap.adjoint`; its anti-multiplicativity is
`LinearMap.adjoint_comp` and its involutivity `LinearMap.adjoint_adjoint`
(both reused as-is, not restated here). -/

/-- Conjugation of a linear map relative to the canonical bases:
`f^C = conjV ∘ f ∘ conjV`, a genuinely ℂ-linear map since the two conjugations
cancel the semilinearity. CoqQ: `conj_lfun` (`hermitian.v:616,1026`). -/
def conjLM (f : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ where
  toFun v := conjV (f (conjV v))
  map_add' u v := by simp [conjV_add]
  map_smul' c v := by simp [conjV_smul]

@[simp]
theorem conjLM_apply (f : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ)
    (v : EuclideanSpace ℂ ι) : conjLM f v = conjV (f (conjV v)) := rfl

/-- Transposition relative to the canonical bases: `f^T = (f^C)†`.
CoqQ: `tr_lfun` (`hermitian.v:617,1030`). -/
noncomputable def transposeLM (f : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.adjoint (conjLM f)

variable (f : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ)

/-- CoqQ `conj_lfunK` (`hermitian.v:1099`): C is involutive. -/
@[simp]
theorem conjLM_conjLM : conjLM (conjLM f) = f :=
  LinearMap.ext fun v => by simp

/-- A ∘ C = T, definitionally. CoqQ `trfAC` (`hermitian.v:1122`). -/
@[simp]
theorem adjoint_conjLM : LinearMap.adjoint (conjLM f) = transposeLM f := rfl

/-- C and A commute: `(f†)^C = f^T`. CoqQ `trfCA` (`hermitian.v:1124`). -/
theorem transposeLM_eq_conjLM_adjoint :
    transposeLM f = conjLM (LinearMap.adjoint f) :=
  ((LinearMap.eq_adjoint_iff _ _).mpr fun x y => by
    rw [conjLM_apply, inner_conjV_left, LinearMap.adjoint_inner_right,
      conjLM_apply, inner_conjV_right]).symm

/-- C ∘ A = T. CoqQ `trfCA`. -/
@[simp]
theorem conjLM_adjoint : conjLM (LinearMap.adjoint f) = transposeLM f :=
  (transposeLM_eq_conjLM_adjoint f).symm

/-- T ∘ C = A. CoqQ `adjfTC` (`hermitian.v:1126`). -/
@[simp]
theorem transposeLM_conjLM : transposeLM (conjLM f) = LinearMap.adjoint f := by
  rw [← adjoint_conjLM, conjLM_conjLM]

/-- C ∘ T = A. CoqQ `adjfCT` (`hermitian.v:1128`). -/
@[simp]
theorem conjLM_transposeLM : conjLM (transposeLM f) = LinearMap.adjoint f := by
  rw [transposeLM_eq_conjLM_adjoint, conjLM_conjLM]

/-- A ∘ T = C. CoqQ `conjfAT` (`hermitian.v:1130`). -/
@[simp]
theorem adjoint_transposeLM : LinearMap.adjoint (transposeLM f) = conjLM f := by
  rw [← adjoint_conjLM, LinearMap.adjoint_adjoint]

/-- T ∘ A = C. CoqQ `conjfTA` (`hermitian.v:1129`). -/
@[simp]
theorem transposeLM_adjoint : transposeLM (LinearMap.adjoint f) = conjLM f := by
  rw [transposeLM_eq_conjLM_adjoint, LinearMap.adjoint_adjoint]

/-- CoqQ `tr_lfunK` (`hermitian.v:1101`): T is involutive. -/
@[simp]
theorem transposeLM_transposeLM : transposeLM (transposeLM f) = f := by
  rw [transposeLM_eq_conjLM_adjoint (transposeLM f), adjoint_transposeLM, conjLM_conjLM]

/-- C is multiplicative. CoqQ `conj_lfun_comp` (`hermitian.v:1103`). -/
theorem conjLM_comp (g : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ μ)
    (f : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ) :
    conjLM (g ∘ₗ f) = conjLM g ∘ₗ conjLM f :=
  LinearMap.ext fun v => by simp

/-- T is anti-multiplicative. CoqQ `tr_lfun_comp` (`hermitian.v:1105`). -/
theorem transposeLM_comp (g : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ μ)
    (f : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ) :
    transposeLM (g ∘ₗ f) = transposeLM f ∘ₗ transposeLM g := by
  rw [← adjoint_conjLM, conjLM_comp, LinearMap.adjoint_comp]
  rfl

/-- C is conjugate-linear in scalars. CoqQ `conj_lfun_scale`. -/
theorem conjLM_smul (c : ℂ) : conjLM (c • f) = star c • conjLM f :=
  LinearMap.ext fun v => by simp [conjV_smul]

/-- T is ℂ-linear in scalars. CoqQ `tr_lfun_scale`. -/
theorem transposeLM_smul (c : ℂ) : transposeLM (c • f) = c • transposeLM f := by
  rw [← adjoint_conjLM, conjLM_smul, map_smulₛₗ, adjoint_conjLM]
  simp

/-- C is additive. CoqQ `conj_lfun` linearity (`hermitian.v:1026`). -/
theorem conjLM_add (g : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ) :
    conjLM (f + g) = conjLM f + conjLM g :=
  LinearMap.ext fun v => by simp [conjV_add]

/-- C preserves zero. -/
@[simp]
theorem conjLM_zero :
    conjLM (0 : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ) = 0 :=
  LinearMap.ext fun v => PiLp.ext fun i => by simp

/-- C is additive over finite sums (from `conjLM_add`/`conjLM_zero`; `conjLM`
is unbundled, so `map_sum` does not apply). -/
theorem conjLM_sum {α : Type*} (s : Finset α)
    (φ : α → (EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ)) :
    conjLM (∑ a ∈ s, φ a) = ∑ a ∈ s, conjLM (φ a) := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, conjLM_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, conjLM_add, ih]

/-- T is additive. CoqQ `tr_lfun` linearity (`hermitian.v:1030`). -/
theorem transposeLM_add (g : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ) :
    transposeLM (f + g) = transposeLM f + transposeLM g := by
  rw [← adjoint_conjLM, conjLM_add, map_add, adjoint_conjLM, adjoint_conjLM]

/-- T preserves zero. -/
@[simp]
theorem transposeLM_zero :
    transposeLM (0 : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ) = 0 := by
  rw [← adjoint_conjLM, conjLM_zero, map_zero]

/-- C on outer products. CoqQ `conj_outp` (`hermitian.v:1141`). -/
theorem conjLM_outerLM (u : EuclideanSpace ℂ κ) (v : EuclideanSpace ℂ ι) :
    conjLM (outerLM u v) = outerLM (conjV u) (conjV v) := by
  refine LinearMap.ext fun x => ?_
  simp only [conjLM_apply, outerLM_apply, conjV_smul, RCLike.star_def, inner_conj_symm]
  rw [inner_conjV_left]

/-- T on outer products. CoqQ `tr_outp` (`hermitian.v:1142`). -/
theorem transposeLM_outerLM (u : EuclideanSpace ℂ κ) (v : EuclideanSpace ℂ ι) :
    transposeLM (outerLM u v) = outerLM (conjV v) (conjV u) := by
  rw [← adjoint_conjLM, conjLM_outerLM, adjoint_outerLM]

end ConjV

/-! ## F-4: operator predicates -/

section Predicates

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- An effect (observable) operator: `0 ≤ f ≤ 1` in the Löwner order
(mathlib's `LinearMap.instLoewnerPartialOrder`, a global instance).
CoqQ: `obslf` (`quantum.v:342`). -/
def IsEffect (f : E →ₗ[ℂ] E) : Prop :=
  0 ≤ f ∧ f ≤ 1

/-- `IsEffect` unfolded to positivity of `f` and `1 - f`. -/
theorem isEffect_iff (f : E →ₗ[ℂ] E) :
    IsEffect f ↔ f.IsPositive ∧ (1 - f).IsPositive :=
  and_congr (LinearMap.nonneg_iff_isPositive f) (LinearMap.le_def f 1)

theorem isEffect_zero : IsEffect (0 : E →ₗ[ℂ] E) :=
  ⟨le_rfl, by rw [LinearMap.le_def]; simp⟩

theorem isEffect_one : IsEffect (1 : E →ₗ[ℂ] E) :=
  ⟨by rw [LinearMap.le_def]; simp, le_rfl⟩

theorem IsEffect.isPositive {f : E →ₗ[ℂ] E} (hf : IsEffect f) : f.IsPositive :=
  (LinearMap.nonneg_iff_isPositive f).mp hf.1

/-- A partial density operator: positive with trace at most `1`.

The trace bound is stated on the real part: for a positive operator the trace
is a nonnegative real (`LinearMap.IsPositive.trace_nonneg`, whose `0 ≤ ·` lives
in the scoped `ComplexOrder`), so no information is lost, and taking `.re`
keeps the definition usable without opening that scope.
CoqQ: `denlf` (`quantum.v:351`). -/
def IsDensity (f : E →ₗ[ℂ] E) : Prop :=
  f.IsPositive ∧ (LinearMap.trace ℂ E f).re ≤ 1

/-- A density operator: positive with trace exactly `1`.
CoqQ: `den1lf` (`quantum.v:360`). -/
def IsDensity1 (f : E →ₗ[ℂ] E) : Prop :=
  f.IsPositive ∧ LinearMap.trace ℂ E f = 1

open scoped ComplexOrder in
/-- Q-2 bridge (spec 04): `IsDensity` in the literal CoqQ form `Tr ρ ≤ 1`, with
`≤` from the scoped `ComplexOrder`. For a positive map the trace is a
nonnegative real, so the stored real-part bound carries the same content.
CoqQ: `denlf` (`quantum.v:350`). -/
theorem isDensity_iff (f : E →ₗ[ℂ] E) :
    IsDensity f ↔ f.IsPositive ∧ LinearMap.trace ℂ E f ≤ 1 := by
  unfold IsDensity
  refine and_congr_right fun hf => ?_
  have him : (LinearMap.trace ℂ E f).im = 0 := by
    simpa using (Complex.le_def.mp hf.trace_nonneg).2.symm
  rw [Complex.le_def, Complex.one_re, Complex.one_im]
  exact (and_iff_left him).symm

theorem isDensity_zero : IsDensity (0 : E →ₗ[ℂ] E) :=
  ⟨LinearMap.isPositive_zero, by simp⟩

theorem IsDensity1.isDensity {f : E →ₗ[ℂ] E} (hf : IsDensity1 f) : IsDensity f :=
  ⟨hf.1, by rw [hf.2]; simp⟩

/-- `|u⟩⟨u|` is positive. CoqQ `outp_psdlf`. -/
theorem isPositive_outerLM_self (u : E) : (outerLM u u).IsPositive := by
  constructor
  · intro x y
    simp only [outerLM_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
    exact mul_comm _ _
  · intro x
    simp only [outerLM_apply, inner_smul_left, RCLike.conj_mul, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
    positivity

/-- `|u⟩⟨u|` for a unit vector `u` is a density operator. CoqQ `outp_den1lf`. -/
theorem isDensity1_outerLM_self [FiniteDimensional ℂ E] {u : E} (hu : ‖u‖ = 1) :
    IsDensity1 (outerLM u u) :=
  ⟨isPositive_outerLM_self u, by
    rw [trace_outerLM, inner_self_eq_norm_sq_to_K, hu]; norm_num⟩

/-- A projection operator: symmetric idempotent. This is exactly mathlib's
`LinearMap.IsSymmetricProjection` (a two-field structure; the conjunction form
is `LinearMap.isSymmetricProjection_iff`), which we reuse rather than duplicate.
CoqQ: `projlf` (`quantum.v:369`). -/
abbrev IsProjOp (f : E →ₗ[ℂ] E) : Prop :=
  f.IsSymmetricProjection

theorem isProjOp_zero : IsProjOp (0 : E →ₗ[ℂ] E) := ⟨.zero, .zero⟩

theorem isProjOp_one : IsProjOp (1 : E →ₗ[ℂ] E) := ⟨.one, .id⟩

/-- `|u⟩⟨u|` for a unit vector `u` is a projection. CoqQ `outp_projlf`. -/
theorem isProjOp_outerLM_self {u : E} (hu : ‖u‖ = 1) : IsProjOp (outerLM u u) :=
  InnerProductSpace.isSymmetricProjection_rankOne_self hu

/-- An isometry: preserves all inner products.
CoqQ: `isolf` (`quantum.v:378`). -/
def IsIsometryOp (f : E →ₗ[ℂ] F) : Prop :=
  ∀ u v, ⟪f u, f v⟫ = ⟪u, v⟫

theorem isIsometryOp_one : IsIsometryOp (1 : E →ₗ[ℂ] E) := fun _ _ => rfl

theorem IsIsometryOp.comp {g : F →ₗ[ℂ] G} {f : E →ₗ[ℂ] F}
    (hg : IsIsometryOp g) (hf : IsIsometryOp f) : IsIsometryOp (g ∘ₗ f) := fun u v => by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hg, hf]

/-- CoqQ `isolf_giso`: an isometry satisfies `f† ∘ f = 1`. -/
theorem IsIsometryOp.adjoint_comp_self [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {f : E →ₗ[ℂ] F} (hf : IsIsometryOp f) : LinearMap.adjoint f ∘ₗ f = LinearMap.id := by
  refine LinearMap.ext fun x => ext_inner_left ℂ fun y => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, hf, LinearMap.id_apply]

end Predicates

/-! ## Rank-one effects and unit vectors -/

section RankOne

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A projection is an effect: both `P` and `1 - P` are of the form `f†f`. -/
theorem isEffect_of_isProjOp {f : E →ₗ[ℂ] E} (hf : IsProjOp f) : IsEffect f := by
  have hadj : LinearMap.adjoint f = f := hf.isSymmetric.adjoint_eq
  have hid : f ∘ₗ f = f := hf.isIdempotentElem
  refine (isEffect_iff f).mpr ⟨?_, ?_⟩
  · rw [show f = LinearMap.adjoint f ∘ₗ f by rw [hadj, hid]]
    exact LinearMap.isPositive_adjoint_comp_self f
  · rw [show (1 - f) = LinearMap.adjoint (1 - f) ∘ₗ (1 - f) by
      rw [map_sub, hadj, LinearMap.adjoint_one]
      simp only [LinearMap.sub_comp, LinearMap.comp_sub, Module.End.one_eq_id,
        LinearMap.id_comp, LinearMap.comp_id, hid]
      abel]
    exact LinearMap.isPositive_adjoint_comp_self _

/-- The projector onto a unit vector is an effect, hence an assertion. -/
theorem isEffect_outerLM_self {u : E} (hu : ‖u‖ = 1) : IsEffect (outerLM u u) :=
  isEffect_of_isProjOp (isProjOp_outerLM_self hu)

/-- Conjugating a rank-one operator conjugates its two vectors — the reason
`unitaryPre` of a pure-state projector is again a pure-state projector. -/
theorem adjoint_comp_outerLM_comp (K : E →ₗ[ℂ] E) (u v : E) :
    LinearMap.adjoint K ∘ₗ outerLM u v ∘ₗ K
      = outerLM (LinearMap.adjoint K u) (LinearMap.adjoint K v) := by
  rw [← LinearMap.comp_assoc, comp_outerLM]
  exact LinearMap.ext fun w => by
    simp only [LinearMap.comp_apply, outerLM_apply, LinearMap.adjoint_inner_left]

theorem norm_eq_one_of_inner_self {v : E} (h : ⟪v, v⟫ = 1) : ‖v‖ = 1 := by
  have h2 : ((‖v‖ : ℝ) : ℂ) ^ 2 = 1 := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) v).symm.trans h
  have h3 : ‖v‖ ^ 2 = 1 := by exact_mod_cast h2
  nlinarith [norm_nonneg v]

end RankOne

end Qhl
