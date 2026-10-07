import Qhl.Dirac.WFInstances

/-!
# D-11 gate benchmark: support inference on 10 representative expressions

Roadmap M5 gate (spec 05): typeclass support-inference is exercised on 10
nested `⊗ᴰ/∘ᴰ/·ᴰ/†ᴰ` expressions over abstract registers `S T U : Finset L`
with ket/bra/lifted-operator leaves. Each `example` asserts the support that
instance search must *synthesize* (symbolic, uncollapsed: `∅ ∪ S` etc.);
failures are recorded as comments. Extra probes: `retypeWF`/`wf_at`
normalization of computed supports, `∑`/`∏` rules.

All rows elaborate with the default `maxHeartbeats` (no `set_option`
anywhere); heartbeat counts are recorded in the M5 gate report.
-/

namespace Qhl.WFTest

open Finset Qhl.Dirac
open scoped Qhl

variable {L : Type*} [Fintype L] [DecidableEq L] {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] {S T U : Finset L}

variable (u : HS D S) (v : HS D T) (w : HS D (S ∪ T))
  (A : EndM D S) (B : LinM D S T) (C : LinM D T U)

/-! ## The 10 gate rows -/

/-- Row 1: composition of lifted operators (middle set `S` unified). -/
example : WF ((⌈B⌉ᴰ : Dirac D) ∘ᴰ ⌈A⌉ᴰ) S T := inferInstance

/-- Row 2: tensor of kets (symbolic union support). -/
example : WF ((∣u⟩ᴰ : Dirac D) ⊗ᴰ ∣v⟩ᴰ) (∅ ∪ ∅) (S ∪ T) := inferInstance

/-- Row 3: operator acting on a ket through `·ᴰ` (the `S' ∪ (S \ T')`
shape, uncollapsed). -/
example : WF ((⌈A⌉ᴰ : Dirac D) ·ᴰ ∣u⟩ᴰ) (∅ ∪ (S \ S)) (S ∪ (S \ S)) :=
  inferInstance

/-- Row 4: adjoint of a ket (support transposed to a bra's). -/
example : WF ((∣u⟩ᴰ : Dirac D)†ᴰ) S ∅ := inferInstance

/-- Row 5: outer product `∣u⟩⟨u∣` (comp through the middle set `∅`). -/
example : WF ((∣u⟩ᴰ : Dirac D) ∘ᴰ (∣u⟩ᴰ)†ᴰ) S S := inferInstance

/-- Row 6: interchange shape — tensor of operators applied to a tensor of
kets (nested middle-set unification `S ∪ T`). -/
example : WF (((⌈B⌉ᴰ : Dirac D) ⊗ᴰ ⌈C⌉ᴰ) ∘ᴰ (∣u⟩ᴰ ⊗ᴰ ∣v⟩ᴰ)) (∅ ∪ ∅) (T ∪ U) :=
  inferInstance

/-- Row 7: `·ᴰ` against a tensor of kets (fully symbolic dot support). -/
example : WF ((⌈A⌉ᴰ : Dirac D) ·ᴰ (∣u⟩ᴰ ⊗ᴰ ∣v⟩ᴰ))
    ((∅ ∪ ∅) ∪ (S \ (S ∪ T))) (S ∪ ((S ∪ T) \ S)) := inferInstance

/-- Row 8: squared norm shape `(B∣u⟩)† ∘ (B∣u⟩)` — a labelled scalar. -/
example : WF (((⌈B⌉ᴰ : Dirac D) ∘ᴰ ∣u⟩ᴰ)†ᴰ ∘ᴰ (⌈B⌉ᴰ ∘ᴰ ∣u⟩ᴰ)) ∅ ∅ :=
  inferInstance

/-- Row 9: module operations mixed with `∘ᴰ` and `𝟙ᴰ` (all at `(S, S)`). -/
example : WF ((2 : ℂ) • (⌈A⌉ᴰ : Dirac D) - ⌈A⌉ᴰ ∘ᴰ ⌈A⌉ᴰ + 𝟙ᴰ S) S S :=
  inferInstance

/-- Row 10: resolution-of-identity shape, a `∑` of outer products. -/
example : WF (∑ k : QIdx D S, (∣deltav D k⟩ᴰ : Dirac D) ∘ᴰ (∣deltav D k⟩ᴰ)†ᴰ)
    S S := inferInstance

/-! ## Edge probes (beyond the 10 rows) -/

/-- Probe E1: `retypeWF` collapses the computed support `(∅ ∪ ∅, S ∪ T)` of
row 2 to the intended `(∅, S ∪ T)`. -/
example : WF ((∣u⟩ᴰ : Dirac D) ⊗ᴰ ∣v⟩ᴰ) ∅ (S ∪ T) :=
  retypeWF ∅ (S ∪ T) _

/-- Probe E2: `wf_at` produces the cleaned `WFAt` fact directly (the form the
labelled laws consume). -/
example : Dirac.WFAt ∅ (S ∪ T) ((∣u⟩ᴰ : Dirac D) ⊗ᴰ ∣v⟩ᴰ) :=
  wf_at ∅ (S ∪ T) _

/- Probe E4 — the known failure shape (union-order mismatch in the middle
set). With `w : HS D (S ∪ T)`:

  example : WF ((⟨w∣ᴰ : Dirac D) ∘ᴰ (∣v⟩ᴰ ⊗ᴰ ∣u⟩ᴰ)) ∅ ∅ := inferInstance

-- FAILS: "failed to synthesize (⟨w∣ᴰ ∘ᴰ ∣v⟩ᴰ ⊗ᴰ ∣u⟩ᴰ).WF ∅ ∅" — the tensor
-- synthesizes target `T ∪ S`, the bra demands middle `S ∪ T`, and outParam
-- unification is syntactic (CoqQ's canonical instances share exactly this
-- limitation). Recovery below: drop to the `WFAt` layer for the offending
-- operand only, letting `wf_at` re-annotate `(∅ ∪ ∅, T ∪ S)` to
-- `(∅, S ∪ T)` via `finset_dec`. -/
example : Dirac.WFAt ∅ ∅ ((⟨w∣ᴰ : Dirac D) ∘ᴰ (∣v⟩ᴰ ⊗ᴰ ∣u⟩ᴰ)) :=
  (wf_bra w).comp (wf_at ∅ (S ∪ T) _)

/-- Probe E3: the higher-order `∏` rule, on a family of kets over pairwise
registers `f : ι → Finset L` (function out-params `Sf`/`Tf` assigned by
pattern unification). -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → Finset L)
    (x : ∀ j, HS D (f j)) :
    WF (∏ j, (∣x j⟩ᴰ : Dirac D)) ((univ : Finset ι).biUnion fun _ => ∅)
      (univ.biUnion f) := inferInstance

end Qhl.WFTest
