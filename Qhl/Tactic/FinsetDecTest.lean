import Qhl.Tactic.FinsetDec

/-!
# Benchmark for `finset_dec` (Decision H3, spec 02 §7)

Every `example` below is closed by `finset_dec` alone. The goals are the
side conditions actually arising in the development: the cast identities in
`dotf`/`sdotf`/`liftF` (`Qhl.HSpace.DotF`, `Qhl.HSpace.LiftF`), the
disjointness hypotheses of `tenf_apply`/`tenf_comp`, and the D-L1..D-L8
side conditions of spec 03 §4.
-/

variable {L : Type*} [DecidableEq L] (S T W U S' T' S₁ S₂ S₃ T₁ T₂ T₃ : Finset L)

/-! ## Pure union identities (cast bookkeeping) -/

example : S ∪ T = T ∪ S := by finset_dec
example : S ∪ (T ∪ W) = (S ∪ T) ∪ W := by finset_dec
example : S ∪ ∅ = S := by finset_dec

/-! ## Union/sdiff identities (`dotf`/`sdotf`/`liftF` definitions) -/

-- `union_sdiff_symm`, the `dotf` codomain identity
example : T' ∪ (S \ T') = S ∪ (T' \ S) := by finset_dec
-- `union_sdiff_self_eq_union` (+ comm), the `sdotf` recasts
example : S ∪ (T \ S) = S ∪ T := by finset_dec
example : T ∪ (S \ T) = S ∪ T := by finset_dec
-- `union_sdiff_of_subset`, the `liftF` identity
example (h : S ⊆ T) : S ∪ (T \ S) = T := by finset_dec
-- `union_sdiff_left`, the `sdotf`-via-`liftF` legs (LiftF.lean `eP`/`eQ`)
example : S₂ \ S₁ = (S₁ ∪ S₂) \ S₁ := by finset_dec
-- absorption (D-L6)
example (h : S ⊆ W) : S ∪ W = W := by finset_dec
-- `dotf_comp` (D-L2) cast identity
example : W = W ∪ (S \ S) := by finset_dec

/-! ## Subset side conditions (`liftF_sdot`, `liftF_liftF`) -/

example (h : S₁ ∪ S₂ ⊆ T) : S₁ ⊆ T := by finset_dec
example (h₁ : S ⊆ T) (h₂ : T ⊆ U) : S ⊆ U := by finset_dec
example : T \ S ⊆ T := by finset_dec
example (h : S ⊆ T) : U \ T ⊆ U \ S := by finset_dec

/-! ## Unconditional disjointness (`liftF`, `dotf_comp`) -/

example : Disjoint S (T \ S) := by finset_dec
example : Disjoint (S \ T) (T \ S) := by finset_dec

/-! ## Disjointness from hypotheses -/

example (h : Disjoint S T) : Disjoint (S \ W) T := by finset_dec
-- redundant hypotheses must not derail the tactic (`_h₂` is not needed)
example (h₁ : Disjoint S₁ S₂) (_h₂ : Disjoint T₁ T₂) :
    Disjoint (S₁ ∪ T₁ \ S₂) (S₂ ∩ T₂) := by finset_dec
example (h₁ : Disjoint S₁ S₂) (h₂ : Disjoint T₁ T₂) :
    Disjoint (S₁ \ W ∪ T₁) (S₂ ∩ T₂) := by finset_dec
-- D-L4 discharged from stronger pairwise disjointness (M5 usage)
example (h : Disjoint S₁ S₂) : Disjoint S₂ (S₁ \ T₂) := by finset_dec
example (h : Disjoint S₂ S₃) : Disjoint S₂ (S₃ \ T₂) ∧ Disjoint (S₃ \ T₂) S₂ := by
  constructor <;> finset_dec

/-! ## `dotf_ten` (D-L1) cast identities from `Disjoint S T'` -/

example (hd : Disjoint S T') : S ∪ S' = S' ∪ (S \ T') := by finset_dec
example (hd : Disjoint S T') : T ∪ T' = T ∪ (T' \ S) := by finset_dec

/-! ## `dotdC` (D-L5) domain identity from the two disjointness conditions -/

example (h₁ : Disjoint S T') (h₂ : Disjoint T S') :
    S' ∪ (S \ T') = S ∪ (S' \ T) := by finset_dec

/-! ## `dotf_assoc` (D-L4) — the interchange conditions and identity-leg
identities of `Qhl.HSpace.DotF.dotf_assoc`, verbatim -/

-- `disjL` from `P1`
example (P1 : Disjoint S₂ (S₁ \ T₂)) :
    Disjoint (S₂ ∪ T₃ \ S₂) (S₁ \ (T₂ ∪ T₃ \ S₂)) := by finset_dec
-- `disjR` from `P2`
example (P2 : Disjoint T₂ (T₃ \ S₂)) :
    Disjoint (S₁ ∪ T₂ \ S₁) (T₃ \ (S₂ ∪ S₁ \ T₂)) := by finset_dec
-- `eX₁` from `P2`
example (P2 : Disjoint T₂ (T₃ \ S₂)) :
    (T₂ ∪ T₃ \ S₂) \ S₁ = T₂ \ S₁ ∪ T₃ \ (S₂ ∪ S₁ \ T₂) := by finset_dec
-- `eX₂`, unconditional
example : T₃ \ S₂ ∪ S₁ \ (T₂ ∪ T₃ \ S₂) = S₁ \ T₂ ∪ T₃ \ (S₂ ∪ S₁ \ T₂) := by
  finset_dec
-- `eX₃` from `P1`
example (P1 : Disjoint S₂ (S₁ \ T₂)) :
    S₂ \ T₃ ∪ S₁ \ (T₂ ∪ T₃ \ S₂) = (S₂ ∪ S₁ \ T₂) \ T₃ := by finset_dec
-- the outer cast identities `h₁`/`h₂` of `dotf_assoc` from `P1`/`P2`
example (P1 : Disjoint S₂ (S₁ \ T₂)) :
    (S₃ ∪ S₂ \ T₃) ∪ S₁ \ (T₂ ∪ T₃ \ S₂) = S₃ ∪ (S₂ ∪ S₁ \ T₂) \ T₃ := by
  finset_dec
example (P2 : Disjoint T₂ (T₃ \ S₂)) :
    T₁ ∪ (T₂ ∪ T₃ \ S₂) \ S₁ = (T₁ ∪ T₂ \ S₁) ∪ T₃ \ (S₂ ∪ S₁ \ T₂) := by
  finset_dec

/-! ## Negative control

`finset_dec` fails (with `grind` failed, in well under a second) rather than
proving nonsense; checked interactively, kept out of the build:
```
example : Disjoint S T := by finset_dec                  -- error: `grind` failed
example (h : Disjoint S T) : S ∪ T = T := by finset_dec  -- error: `grind` failed
```
-/
