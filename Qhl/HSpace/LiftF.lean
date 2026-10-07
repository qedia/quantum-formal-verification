import Qhl.HSpace.DotF
import Qhl.Foundations.Order

/-!
# Labelled Hilbert spaces: cylindrical extension and positivity

Mirror of the lifting/positivity layer of `CoqQ/src/dirac/hstensor.v` (spec 02
§6, subgoals H-20 and H-21, milestone M3).

* Bridging lemmas: `castF_isPositive_iff`, `castF_le_castF_iff`,
  `isIsometryOp_of_adjoint_comp_self`
* H-21: `tenf_isPositive` (CoqQ `tenf_ge0`), `tenf_eq_zero_iff` (CoqQ
  `tenf_eq0`, generalized to rectangular maps — this needs disjointness of
  *both* the domain and codomain label sets, see the docstring)
* H-20: `liftF D h f` — cylindrical extension `castF … (f ⊗ᶠ 1)` (CoqQ
  `lift_lf`), with entry formula `liftF_deltav_apply`, linearity, `liftF_one`,
  multiplicativity `liftF_comp`, transitivity `liftF_liftF`, A/C/T
  preservation, order embedding `liftF_le_liftF_iff`, injectivity
  `liftF_injective`, the predicate-closure iffs (CoqQ `lift_lf_*E`), and
  `sdotf_eq_liftF_comp`/`liftF_sdot` (CoqQ `lift_lf_sdot`)

The downward direction from `HS D T` to `HS D S` (order embedding,
injectivity, and hence every predicate-closure *iff*) requires the
classical-state types to be nonempty (`[∀ i, Nonempty (D i)]`): if some `D i`
with `i ∈ T \ S` were empty, `HS D T` would be the zero space while `HS D S`
need not be, so `liftF` could not be injective. CoqQ's Hilbert spaces have
positive dimension, so this hypothesis is implicit there.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace ComplexOrder

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {S T U S' T' S₁ S₂ T₁ T₂ : Finset L}

/-! ## Bridging lemmas: casts vs. positivity and order -/

/-- Positivity is invariant under endomorphism casts. -/
@[simp, cast_simps]
theorem castF_isPositive_iff (h : S = T) (f : EndM D S) :
    (castF D h h f).IsPositive ↔ f.IsPositive := by
  subst h; simp

/-- The Löwner order is invariant under endomorphism casts. -/
@[simp, cast_simps]
theorem castF_le_castF_iff (h : S = T) (f g : EndM D S) :
    castF D h h f ≤ castF D h h g ↔ f ≤ g := by
  subst h; simp

/-- Converse of `IsIsometryOp.adjoint_comp_self`: `f† ∘ₗ f = 1` makes `f` an
isometry. -/
theorem isIsometryOp_of_adjoint_comp_self {f : LinM D S T}
    (hf : LinearMap.adjoint f ∘ₗ f = 1) : IsIsometryOp f := fun u v => by
  rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, hf,
    Module.End.one_apply]

/-! ## H-21: positivity and non-degeneracy of the operator tensor -/

/-- CoqQ `tenf_ge0` (`hstensor.v:2890`): the tensor of positive endomorphisms
of disjoint registers is positive. Route: factor both maps as `a† ∘ₗ a`
(F-L6), then `f ⊗ᶠ g = (a ⊗ᶠ b)† ∘ₗ (a ⊗ᶠ b)` by the interchange law. -/
theorem tenf_isPositive (hd : Disjoint S T) {f : EndM D S} {g : EndM D T}
    (hf : f.IsPositive) (hg : g.IsPositive) : (tenf D f g).IsPositive := by
  obtain ⟨a, rfl⟩ := (isPositive_iff_exists_adjoint_comp f).mp hf
  obtain ⟨b, rfl⟩ := (isPositive_iff_exists_adjoint_comp g).mp hg
  rw [tenf_comp D hd, ← adjoint_tenf]
  exact LinearMap.isPositive_adjoint_comp_self _

/-- CoqQ `tenf_eq0` (`hstensor.v:2897`), generalized to rectangular maps: the
operator tensor vanishes iff a factor vanishes. Both disjointness hypotheses
are needed in the rectangular case (e.g. for kets `f = |0⟩`, `g = |1⟩` on the
same codomain register, `f ⊗ᶠ g = 0` with both factors nonzero); for CoqQ's
endomorphism version they coincide. The `⇐` direction is unconditional. -/
theorem tenf_eq_zero_iff (hd₁ : Disjoint S₁ S₂) (hd₂ : Disjoint T₁ T₂)
    (f : LinM D S₁ T₁) (g : LinM D S₂ T₂) :
    tenf D f g = 0 ↔ f = 0 ∨ g = 0 := by
  refine ⟨fun h0 => ?_, ?_⟩
  · by_contra hc
    push Not at hc
    obtain ⟨hf, hg⟩ := hc
    obtain ⟨k₁, l₁, hf₁⟩ : ∃ k l, f (deltav D k) l ≠ 0 := by
      by_contra he
      push Not at he
      exact hf (linM_ext D fun k => PiLp.ext fun l => by simpa using he k l)
    obtain ⟨k₂, l₂, hg₂⟩ : ∃ k l, g (deltav D k) l ≠ 0 := by
      by_contra he
      push Not at he
      exact hg (linM_ext D fun k => PiLp.ext fun l => by simpa using he k l)
    have hE : tenf D f g (deltav D (QIdx.merge D k₁ k₂)) (QIdx.merge D l₁ l₂) = 0 := by
      rw [h0]
      simp
    simp only [tenf_deltav, tenv_apply, QIdx.res_merge_left,
      QIdx.res_merge_right D hd₁, QIdx.res_merge_right D hd₂] at hE
    rcases mul_eq_zero.mp hE with h | h
    exacts [hf₁ h, hg₂ h]
  · rintro (rfl | rfl)
    · exact tenf_zero_left D g
    · exact tenf_zero_right D f

/-! ## H-20: the cylindrical extension `liftF` -/

/-- Cylindrical extension of an endomorphism of a subregister: tensor with the
identity on `T \ S` and cast along `S ∪ (T \ S) = T`. CoqQ `lift_lf`
(`hstensor.v:3390`). -/
noncomputable def liftF (h : S ⊆ T) (f : EndM D S) : EndM D T :=
  castF D (union_sdiff_of_subset h) (union_sdiff_of_subset h)
    (tenf D f (1 : EndM D (T \ S)))

/-- Matrix entries of the extension: the entry of `f` at the restricted states
times the Kronecker delta on `T \ S`. -/
@[simp, HS_simps]
theorem liftF_deltav_apply (h : S ⊆ T) (f : EndM D S) (k l : QIdx D T) :
    liftF D h f (deltav D k) l =
      f (deltav D (QIdx.res D h k)) (QIdx.res D h l) *
        if QIdx.res D (sdiff_subset : T \ S ⊆ T) l =
            QIdx.res D (sdiff_subset : T \ S ⊆ T) k then 1 else 0 := by
  simp only [liftF, castF_apply, castH_deltav, tenf_deltav, castH_apply, tenv_apply,
    QIdx.res_cast, Module.End.one_apply, deltav_apply]

/-- `liftF` acts as `f` on the `S`-factor of a split vector. -/
theorem liftF_castH_tenv (h : S ⊆ T) (f : EndM D S) (u : HS D S)
    (v : HS D (T \ S)) :
    liftF D h f (castH D (union_sdiff_of_subset h) (tenv D u v)) =
      castH D (union_sdiff_of_subset h) (tenv D (f u) v) := by
  simp only [liftF, castF_apply, castH_castH, castH_rfl,
    LinearIsometryEquiv.coe_refl, id_eq, tenf_apply D disjoint_sdiff,
    Module.End.one_apply]

/-- CoqQ `lift_lf1` (`hstensor.v:3570`). -/
@[simp]
theorem liftF_one (h : S ⊆ T) : liftF D h (1 : EndM D S) = 1 := by
  simp only [liftF, tenf_one_one, castF_one]

@[simp]
theorem liftF_zero (h : S ⊆ T) : liftF D h (0 : EndM D S) = 0 := by
  simp only [liftF, tenf_zero_left, map_zero]

theorem liftF_add (h : S ⊆ T) (f g : EndM D S) :
    liftF D h (f + g) = liftF D h f + liftF D h g := by
  simp only [liftF, tenf_add_left, map_add]

theorem liftF_smul (h : S ⊆ T) (c : ℂ) (f : EndM D S) :
    liftF D h (c • f) = c • liftF D h f := by
  simp only [liftF, tenf_smul_left, map_smul]

theorem liftF_sub (h : S ⊆ T) (f g : EndM D S) :
    liftF D h (f - g) = liftF D h f - liftF D h g := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ g, liftF_add, liftF_smul, neg_one_smul,
    ← sub_eq_add_neg]

/-- CoqQ `lift_lf_comp` (`hstensor.v:3604`): the extension is multiplicative —
*unconditionally* (the interchange side condition `Disjoint S (T \ S)` is
free). -/
theorem liftF_comp (h : S ⊆ T) (f g : EndM D S) :
    liftF D h (f ∘ₗ g) = liftF D h f ∘ₗ liftF D h g := by
  have key : tenf D (f ∘ₗ g) (1 : EndM D (T \ S)) =
      tenf D f (1 : EndM D (T \ S)) ∘ₗ tenf D g (1 : EndM D (T \ S)) := by
    rw [← tenf_comp D disjoint_sdiff, Module.End.one_eq_id, LinearMap.id_comp]
  simp only [liftF, key]
  exact castF_comp D _ (union_sdiff_of_subset h) _ _ _

/-! ### A/C/T preservation (CoqQ `hstensor.v:3595-3603`) -/

/-- CoqQ `lift_lf_adj` — *unconditionally*. -/
@[simp]
theorem adjoint_liftF (h : S ⊆ T) (f : EndM D S) :
    LinearMap.adjoint (liftF D h f) = liftF D h (LinearMap.adjoint f) := by
  simp only [liftF, castF_adj, adjoint_tenf, LinearMap.adjoint_one]

/-- CoqQ `lift_lf_conj` — *unconditionally*. -/
@[simp]
theorem conjLM_liftF (h : S ⊆ T) (f : EndM D S) :
    conjLM (liftF D h f) = liftF D h (conjLM f) := by
  simp only [liftF, castF_conj, conjLM_tenf, conjLM_one]

/-- CoqQ `lift_lf_tr` — *unconditionally*. -/
@[simp]
theorem transposeLM_liftF (h : S ⊆ T) (f : EndM D S) :
    transposeLM (liftF D h f) = liftF D h (transposeLM f) := by
  rw [← adjoint_conjLM, conjLM_liftF, adjoint_liftF, adjoint_conjLM]

/-! ### Transitivity -/

/-- Two states on `U` agree on `U \ S` iff they agree on `T \ S` and on
`U \ T` (for `S ⊆ T ⊆ U`); all restriction proofs are arbitrary so the lemma
matches any `simp` normal form. -/
private theorem res_sdiff_split_iff (h₁ : S ⊆ T) (h₂ : T ⊆ U) (hTS : T \ S ⊆ U)
    (hUT : U \ T ⊆ U) (hUS : U \ S ⊆ U) (k l : QIdx D U) :
    (QIdx.res D hTS l = QIdx.res D hTS k ∧ QIdx.res D hUT l = QIdx.res D hUT k) ↔
      QIdx.res D hUS l = QIdx.res D hUS k := by
  simp only [funext_iff]
  constructor
  · rintro ⟨hA, hB⟩ i
    obtain ⟨hiU, hiS⟩ := mem_sdiff.1 i.2
    by_cases hiT : (i : L) ∈ T
    · exact hA ⟨i, mem_sdiff.2 ⟨hiT, hiS⟩⟩
    · exact hB ⟨i, mem_sdiff.2 ⟨hiU, hiT⟩⟩
  · intro hAB
    refine ⟨fun i => ?_, fun i => ?_⟩
    · obtain ⟨hiT, hiS⟩ := mem_sdiff.1 i.2
      exact hAB ⟨i, mem_sdiff.2 ⟨h₂ hiT, hiS⟩⟩
    · obtain ⟨hiU, hiT⟩ := mem_sdiff.1 i.2
      exact hAB ⟨i, mem_sdiff.2 ⟨hiU, fun hiS => hiT (h₁ hiS)⟩⟩

/-- Merge two Kronecker deltas along an iff of the conditions (applied via
`exact`, so mismatched-but-defeq `Decidable` instances are accepted). -/
private theorem ite_mul_ite_of_iff {P Q R : Prop} [Decidable P] [Decidable Q]
    [Decidable R] (h : P ∧ Q ↔ R) :
    ((if P then (1 : ℂ) else 0) * if Q then 1 else 0) = if R then 1 else 0 := by
  rw [ite_zero_mul_ite_zero, one_mul]
  exact if_congr h rfl rfl

/-- CoqQ `lift_lf2` (`hstensor.v:3694`): consecutive extensions collapse. -/
theorem liftF_liftF (h₁ : S ⊆ T) (h₂ : T ⊆ U) (f : EndM D S) :
    liftF D h₂ (liftF D h₁ f) = liftF D (h₁.trans h₂) f := by
  refine linM_ext D fun k => PiLp.ext fun l => ?_
  simp only [liftF_deltav_apply, QIdx.res_res, mul_assoc]
  exact congrArg₂ (· * ·) rfl
    (ite_mul_ite_of_iff (res_sdiff_split_iff D h₁ h₂ _ _ _ k l))

/-! ### Lifting general products (CoqQ `lift_lf_sdot`) -/

/-- `sdotf` is the composition of the cylindrical extensions to the union —
*unconditional* (no disjointness; this is exactly what `sdotf` exists for). -/
theorem sdotf_eq_liftF_comp (P : EndM D S₁) (Q : EndM D S₂) :
    sdotf D P Q =
      liftF D subset_union_left P ∘ₗ liftF D subset_union_right Q := by
  have eP : S₂ \ S₁ = (S₁ ∪ S₂) \ S₁ := (union_sdiff_left S₁ S₂).symm
  have eQ : S₁ \ S₂ = (S₁ ∪ S₂) \ S₂ := (union_sdiff_right S₁ S₂).symm
  simp only [liftF, sdotf, dotf]
  rw [← tenf_one_congr D eP (by rw [eP]) (by rw [eP]) P,
    ← tenf_one_congr D eQ (by rw [eQ]) (by rw [eQ]) Q]
  exact LinearMap.ext fun _ => rfl

/-- CoqQ `lift_lf_sdot` (`hstensor.v:3758`): lifting a general product is the
product of the liftings — *unconditional* (no disjointness of `S₁`/`S₂`). All
three subset proofs are arbitrary, so the lemma matches any `simp` normal
form. -/
theorem liftF_sdot (h : S₁ ∪ S₂ ⊆ T) (h₁ : S₁ ⊆ T) (h₂ : S₂ ⊆ T)
    (P : EndM D S₁) (Q : EndM D S₂) :
    liftF D h (sdotf D P Q) = liftF D h₁ P ∘ₗ liftF D h₂ Q := by
  rw [sdotf_eq_liftF_comp, liftF_comp, liftF_liftF, liftF_liftF]

/-! ### Positivity, order embedding, injectivity -/

/-- One half of CoqQ `lift_lf_geE` (`hstensor.v:3606-3661`), unconditional:
extensions of positive maps are positive. -/
theorem liftF_isPositive (h : S ⊆ T) {f : EndM D S} (hf : f.IsPositive) :
    (liftF D h f).IsPositive := by
  simp only [liftF]
  exact (castF_isPositive_iff D _ _).mpr
    (tenf_isPositive D disjoint_sdiff hf LinearMap.isPositive_one)

/-- One half of the isometry closure, unconditional: `liftF` of an isometry is
an isometry, since `(liftF f)† ∘ₗ liftF f = liftF (f† ∘ₗ f) = liftF 1 = 1`. -/
theorem liftF_isIsometryOp (h : S ⊆ T) {f : EndM D S} (hf : IsIsometryOp f) :
    IsIsometryOp (liftF D h f) := by
  refine isIsometryOp_of_adjoint_comp_self D ?_
  rw [adjoint_liftF, ← liftF_comp, hf.adjoint_comp_self, ← Module.End.one_eq_id,
    liftF_one]

section Nonempty

variable [∀ i, Nonempty (D i)]

/-- CoqQ `lift_lf_lef` (`hstensor.v:3573`): the extension is an order
embedding. The `⇒` direction tests on vectors `castH … (u ⊗ᵥ δ_v)` and needs a
classical state `v` of `T \ S`, hence the nonemptiness hypothesis. -/
theorem liftF_le_liftF_iff (h : S ⊆ T) (f g : EndM D S) :
    liftF D h f ≤ liftF D h g ↔ f ≤ g := by
  constructor
  · intro hle
    rw [le_iff_inner_le]
    intro u
    have h2 := (le_iff_inner_le _ _).mp hle
      (castH D (union_sdiff_of_subset h)
        (tenv D u (deltav D fun i => Classical.arbitrary (D i))))
    rw [liftF_castH_tenv, liftF_castH_tenv, castH_inner, castH_inner,
      tenv_inner D disjoint_sdiff, tenv_inner D disjoint_sdiff, dv_dot,
      if_pos rfl, mul_one, mul_one] at h2
    exact h2
  · intro hle
    rw [LinearMap.le_def] at hle ⊢
    rw [← liftF_sub D h]
    exact liftF_isPositive D h hle

/-- CoqQ `lift_lf_inj` (`hstensor.v:3580`). -/
theorem liftF_injective (h : S ⊆ T) : Function.Injective (liftF D h) :=
  fun f g hfg =>
    le_antisymm ((liftF_le_liftF_iff D h f g).mp hfg.le)
      ((liftF_le_liftF_iff D h g f).mp hfg.ge)

/-! ### Predicate closure (CoqQ `lift_lf_*E`, `hstensor.v:3606-3661`) -/

/-- CoqQ `lift_lf_geE`: positivity closure, as an iff. -/
theorem liftF_isPositive_iff (h : S ⊆ T) (f : EndM D S) :
    (liftF D h f).IsPositive ↔ f.IsPositive := by
  rw [← LinearMap.nonneg_iff_isPositive, ← LinearMap.nonneg_iff_isPositive,
    ← liftF_zero D h, liftF_le_liftF_iff]

/-- CoqQ `lift_lf_hermE`: self-adjointness closure, as an iff. -/
theorem liftF_isSymmetric_iff (h : S ⊆ T) (f : EndM D S) :
    (liftF D h f).IsSymmetric ↔ f.IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSymmetric_iff_isSelfAdjoint,
    isSelfAdjoint_iff, isSelfAdjoint_iff, LinearMap.star_eq_adjoint,
    LinearMap.star_eq_adjoint, adjoint_liftF]
  exact ⟨fun h' => liftF_injective D h h', fun h' => congrArg (liftF D h) h'⟩

/-- CoqQ `lift_lf_projE`: projection closure, as an iff. -/
theorem liftF_isProjOp_iff (h : S ⊆ T) (f : EndM D S) :
    IsProjOp (liftF D h f) ↔ IsProjOp f := by
  have hidem : IsIdempotentElem (liftF D h f) ↔ IsIdempotentElem f := by
    simp only [IsIdempotentElem, Module.End.mul_eq_comp, ← liftF_comp]
    exact ⟨fun h' => liftF_injective D h h', fun h' => congrArg (liftF D h) h'⟩
  simp only [IsProjOp, LinearMap.isSymmetricProjection_iff]
  exact and_congr hidem (liftF_isSymmetric_iff D h f)

/-- CoqQ `lift_lf_obsE`: effect closure, as an iff. -/
theorem liftF_isEffect_iff (h : S ⊆ T) (f : EndM D S) :
    IsEffect (liftF D h f) ↔ IsEffect f := by
  simp only [IsEffect]
  rw [← liftF_zero D h, ← liftF_one D h, liftF_le_liftF_iff, liftF_le_liftF_iff]

/-- CoqQ `lift_lf_isoE`: isometry closure, as an iff (the converse direction
comes from injectivity applied to `liftF (f† ∘ₗ f) = liftF 1`). -/
theorem liftF_isIsometryOp_iff (h : S ⊆ T) (f : EndM D S) :
    IsIsometryOp (liftF D h f) ↔ IsIsometryOp f := by
  refine ⟨fun hf => isIsometryOp_of_adjoint_comp_self D ?_, liftF_isIsometryOp D h⟩
  have h1 : liftF D h (LinearMap.adjoint f ∘ₗ f) = liftF D h 1 := by
    rw [liftF_comp, ← adjoint_liftF, hf.adjoint_comp_self, liftF_one,
      Module.End.one_eq_id]
  exact liftF_injective D h h1

end Nonempty

end Qhl
