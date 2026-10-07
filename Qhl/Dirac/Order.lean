import Qhl.Dirac.WF

/-!
# The Löwner order on `Dirac`

Mirror of `CoqQ/src/dirac/dirac.v:2312-2531` (spec 03 §7, subgoal D-14).

* `Dirac.IsPsd d` — blockwise positivity: every diagonal block is a positive
  map and every off-diagonal block vanishes (CoqQ `psdd:2317`); closure under
  `0/+/•/∑`, `isPsd_ofBlock_iff`, and self-adjointness `IsPsd.adj_eq`
* `PartialOrder (Dirac D)` with `d ≤ e ↔ IsPsd (e - d)` (CoqQ `led_def:2334`,
  instance `2363`); compatibility: `IsOrderedAddMonoid (Dirac D)` (mirroring
  mathlib's instance for the layer-0 Löwner order) and positive-scalar
  monotonicity `smul_le_smul_of_nonneg_left`
* reduction to the layer-0 Löwner order (mathlib's
  `LinearMap.instLoewnerPartialOrder` on `EndM D S`):
  `ofBlock_le_ofBlock_iff` (CoqQ `lin_lef:2441`), `ofBlock_nonneg_iff`
  (CoqQ `sqr_gef0:2430`), `ofBlock_le_one_iff`/`one_le_ofBlock_iff` and the wf
  forms `IsSqOn.le_iff`/`IsSqOn.nonneg_iff`/`IsSqOn.le_one_iff`/
  `IsSqOn.one_le_iff` (CoqQ `sqr_lef1`-family, `dirac.v:2453-2531`)

Scalars stay in `ℂ` with hypotheses `0 ≤ c` read in the scoped `ComplexOrder`
(the convention of `Qhl.Foundations.Order`). The `bregVOrder` theory of `⊗ᴰ`
vs `≤` (`dirac.v:2533-2756`) is deliberately not ported (spec: on demand).
-/

namespace Qhl

open scoped ComplexOrder

variable {L : Type*} [Fintype L] [DecidableEq L] {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] {S T : Finset L}

namespace Dirac

/-! ## Blockwise positivity (CoqQ `psdd`, `dirac.v:2317`) -/

/-- A Dirac expression is positive semidefinite if every diagonal block is a
positive map and every off-diagonal block vanishes. CoqQ: `psdd`
(`dirac.v:2317`). -/
def IsPsd (d : Dirac D) : Prop :=
  (∀ S : Finset L, (d S S).IsPositive) ∧ ∀ S T : Finset L, S ≠ T → d S T = 0

theorem IsPsd.isPositive {d : Dirac D} (h : IsPsd d) (S : Finset L) :
    (d S S).IsPositive := h.1 S

theorem IsPsd.apply_of_ne {d : Dirac D} (h : IsPsd d) {S T : Finset L}
    (hne : S ≠ T) : d S T = 0 := h.2 S T hne

theorem isPsd_zero : IsPsd (0 : Dirac D) :=
  ⟨fun _ => LinearMap.isPositive_zero, fun _ _ _ => rfl⟩

theorem IsPsd.add {d e : Dirac D} (hd : IsPsd d) (he : IsPsd e) :
    IsPsd (d + e) :=
  ⟨fun S => (hd.1 S).add (he.1 S), fun S T hne => by
    rw [add_apply, hd.2 S T hne, he.2 S T hne, add_zero]⟩

/-- Closure under nonnegative scalars (`0 ≤ c` in the scoped `ComplexOrder`).
CoqQ: `psdd` scaling (`dirac.v:2312-2430`). -/
theorem IsPsd.smul {d : Dirac D} (hd : IsPsd d) {c : ℂ} (hc : 0 ≤ c) :
    IsPsd (c • d) :=
  ⟨fun S => (hd.1 S).smul_of_nonneg hc, fun S T hne => by
    rw [smul_apply, hd.2 S T hne, smul_zero]⟩

theorem IsPsd.sum {α : Type*} {s : Finset α} {d : α → Dirac D}
    (h : ∀ i ∈ s, IsPsd (d i)) : IsPsd (∑ i ∈ s, d i) :=
  ⟨fun S => by
    rw [sum_apply]
    exact LinearMap.isPositive_sum s fun i hi => (h i hi).1 S,
   fun S T hne => by
    rw [sum_apply]
    exact Finset.sum_eq_zero fun i hi => (h i hi).2 S T hne⟩

/-- A single square block is psd iff its block map is positive.
CoqQ: `sqr_gef0`-adjacent (`dirac.v:2430`). -/
theorem isPsd_ofBlock_iff {f : EndM D S} :
    IsPsd (⌈f⌉ᴰ : Dirac D) ↔ f.IsPositive := by
  constructor
  · intro h
    have hS := h.1 S
    rwa [ofBlock_apply_self] at hS
  · intro hf
    refine ⟨fun S' => ?_, fun S' T' hne => ?_⟩
    · by_cases hS : S = S'
      · subst hS
        rwa [ofBlock_apply_self]
      · rw [ofBlock_apply_of_ne_left _ (Ne.symm hS)]
        exact LinearMap.isPositive_zero
    · by_cases hS : S' = S
      · subst hS
        exact ofBlock_apply_of_ne_right _ (Ne.symm hne)
      · exact ofBlock_apply_of_ne_left _ hS

/-- A psd expression is self-adjoint (blockwise: positive maps are symmetric,
off-diagonal blocks vanish on both sides). CoqQ: psd ⊆ hermitian
(`dirac.v:2312-2430`). -/
theorem IsPsd.adj_eq {d : Dirac D} (h : IsPsd d) : d†ᴰ = d := by
  refine Dirac.ext fun S T => ?_
  rw [adj_apply]
  by_cases hST : S = T
  · subst hST
    exact (h.1 S).adjoint_eq
  · rw [h.2 T S (Ne.symm hST), map_zero, h.2 S T hST]

/-! ## The partial order (CoqQ `led_def:2334`, instance `dirac.v:2363`) -/

instance : PartialOrder (Dirac D) where
  le d e := IsPsd (e - d)
  le_refl d := by
    rw [sub_self]
    exact isPsd_zero
  le_trans a b c hab hbc := by
    have h₁ : IsPsd (b - a) := hab
    have h₂ : IsPsd (c - b) := hbc
    change IsPsd (c - a)
    rw [← sub_add_sub_cancel c b a]
    exact h₂.add h₁
  le_antisymm a b hab hba := by
    have h₁ : IsPsd (b - a) := hab
    have h₂ : IsPsd (a - b) := hba
    refine Dirac.ext fun S T => ?_
    by_cases hST : S = T
    · subst hST
      refine le_antisymm ?_ ?_ <;> rw [LinearMap.le_def]
      · have h := h₁.1 S
        rwa [sub_apply] at h
      · have h := h₂.1 S
        rwa [sub_apply] at h
    · rw [← sub_eq_zero]
      have h := h₂.2 S T hST
      rwa [sub_apply] at h

/-- The defining unfold of the order. CoqQ: `led_def` (`dirac.v:2334`). -/
theorem le_def {d e : Dirac D} : d ≤ e ↔ IsPsd (e - d) := Iff.rfl

theorem nonneg_iff_isPsd {d : Dirac D} : 0 ≤ d ↔ IsPsd d := by
  rw [le_def, sub_zero]

/-- Compatibility of the order with `+` (mirrors mathlib's instance for the
layer-0 Löwner order). CoqQ: `dirac.v:2363`-area. -/
instance : IsOrderedAddMonoid (Dirac D) where
  add_le_add_left a b hab c := by
    have h : IsPsd (b - a) := hab
    change IsPsd (b + c - (a + c))
    rwa [add_sub_add_right_eq_sub]

/-- Positive-scalar monotonicity (`0 ≤ c` in the scoped `ComplexOrder`).
CoqQ: `led`-scaling (`dirac.v:2312-2430`). -/
theorem smul_le_smul_of_nonneg_left {d e : Dirac D} (h : d ≤ e) {c : ℂ}
    (hc : 0 ≤ c) : c • d ≤ c • e := by
  rw [le_def, ← smul_sub]
  exact (le_def.mp h).smul hc

/-! ## Reduction to the layer-0 Löwner order (CoqQ `sqr_gef0:2430`,
`lin_lef:2441`, `sqr_lef1`-family `2453-2531`) -/

/-- Same-block comparison reduces to the layer-0 Löwner order.
CoqQ: `lin_lef` (`dirac.v:2441`). -/
theorem ofBlock_le_ofBlock_iff {f g : EndM D S} :
    (⌈f⌉ᴰ : Dirac D) ≤ ⌈g⌉ᴰ ↔ f ≤ g := by
  rw [le_def, ← ofBlock_sub, isPsd_ofBlock_iff]
  exact (LinearMap.le_def f g).symm

/-- CoqQ: `sqr_gef0` (`dirac.v:2430`). -/
theorem ofBlock_nonneg_iff {f : EndM D S} :
    0 ≤ (⌈f⌉ᴰ : Dirac D) ↔ 0 ≤ f := by
  rw [nonneg_iff_isPsd, isPsd_ofBlock_iff, LinearMap.nonneg_iff_isPositive]

/-- CoqQ: `sqr_lef1` (`dirac.v:2453`). -/
theorem ofBlock_le_one_iff {f : EndM D S} :
    (⌈f⌉ᴰ : Dirac D) ≤ 𝟙ᴰ S ↔ f ≤ 1 := by
  rw [one_eq_ofBlock, ofBlock_le_ofBlock_iff]

/-- CoqQ: `sqr_gef1` (`dirac.v:2453-2531`). -/
theorem one_le_ofBlock_iff {f : EndM D S} :
    (𝟙ᴰ S : Dirac D) ≤ ⌈f⌉ᴰ ↔ 1 ≤ f := by
  rw [one_eq_ofBlock, ofBlock_le_ofBlock_iff]

/-- Wf form of `ofBlock_le_ofBlock_iff`: comparison of square wf expressions
on the same registers reduces to their home blocks. CoqQ: `sqr_lefP`-shaped
member of the `sqr_lef1` family (`dirac.v:2453-2531`). -/
theorem IsSqOn.le_iff {d e : Dirac D} (hd : IsSqOn S d) (he : IsSqOn S e) :
    d ≤ e ↔ d S S ≤ e S S := by
  conv_lhs => rw [← hd.eq, ← he.eq]
  exact ofBlock_le_ofBlock_iff

/-- Wf form of `ofBlock_nonneg_iff`. CoqQ: `sqr_gef0` (`dirac.v:2430`). -/
theorem IsSqOn.nonneg_iff {d : Dirac D} (hd : IsSqOn S d) :
    0 ≤ d ↔ (d S S).IsPositive := by
  rw [nonneg_iff_isPsd]
  conv_lhs => rw [← hd.eq]
  exact isPsd_ofBlock_iff

/-- Wf form of `ofBlock_le_one_iff` (the effect condition `d ≤ 𝟙ᴰ S`).
CoqQ: `sqr_lef1` (`dirac.v:2453`). -/
theorem IsSqOn.le_one_iff {d : Dirac D} (hd : IsSqOn S d) :
    d ≤ 𝟙ᴰ S ↔ d S S ≤ 1 := by
  rw [IsSqOn.le_iff hd wf_one, one_apply_self]

/-- Wf form of `one_le_ofBlock_iff`. CoqQ: `sqr_gef1` (`dirac.v:2453-2531`). -/
theorem IsSqOn.one_le_iff {d : Dirac D} (hd : IsSqOn S d) :
    (𝟙ᴰ S : Dirac D) ≤ d ↔ 1 ≤ d S S := by
  rw [IsSqOn.le_iff wf_one hd, one_apply_self]

end Dirac

end Qhl
