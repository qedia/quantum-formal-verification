import Qhl.Dirac.Laws

/-!
# D-11: typeclass support inference for Dirac expressions

Mirror of CoqQ's ~40 `Canonical` wf-instances (`dirac.v:1230-1691`), spec 03
§5 (D-11), roadmap M5 gate: encode the D-10 support table as instances of a
class `Dirac.WF d S T` with `outParam` supports, so that Lean *infers* the
home block of a composite expression.

* `Dirac.WF d S T` — `d` is well-formed at `(S, T)`, with `S`, `T` inferred
* leaf instances: `ofBlock`, `ket`, `bra`, `num`, `one`, ring `1`
* closure instances: `+`, `•`, `-`, `†ᴰ/ᶜᴰ/ᵀᴰ`, `∘ᴰ` (unifying the middle
  set), `⊗ᴰ`/`*` (unions), `·ᴰ` (the `S' ∪ (S \ T')` shape), `∑`, `∏`
* extraction and re-annotation: `Dirac.wf_of`, `Dirac.wf_at`,
  `Dirac.retypeWF` — the latter two clean up computed supports
  (`∅ ∪ S` etc.) via a `finset_dec` autoparam

Known limitation (shared with CoqQ's canonical solution): inferred supports
stay *syntactic*. `∅ ∪ S` does not collapse to `S`, and `∘ᴰ` unifies the
middle set only up to reducible defeq, so `T ∪ S` never matches `S ∪ T`.
The benchmark for the M5 gate lives in `Qhl.Dirac.WFInstancesTest`.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L] {D : L → Type*}
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] {S T W S' T' : Finset L}

namespace Dirac

/-- Well-formedness at an *inferred* block: instance search reconstructs the
home block `(S, T)` of `d` from its syntax, following the D-10 table. CoqQ:
the `wfd`/`sqrd`/`ketd`/`brad` HB structures (`dirac.v:1230-1350`). -/
class WF (d : Dirac D) (S T : outParam (Finset L)) : Prop where
  /-- The underlying unconditional wf fact. -/
  wf : WFAt S T d

/-- Extract the inferred `WFAt` fact of `d` (supports as synthesized). -/
theorem wf_of (d : Dirac D) {S T : Finset L} [h : WF d S T] : WFAt S T d :=
  h.wf

/-- Produce `WFAt S' T' d` from the *inferred* typing of `d`, discharging the
gap between the computed supports and the requested ones by `finset_dec` —
the main cleanup device for symbolic supports like `∅ ∪ S`. -/
theorem wf_at (S' T' : Finset L) (d : Dirac D) {S T : Finset L} [h : WF d S T]
    (h₁ : S = S' := by finset_dec) (h₂ : T = T' := by finset_dec) :
    WFAt S' T' d :=
  h.wf.cast h₁ h₂

/-- Re-annotate an inferred `WF` typing at propositionally equal label sets
(the `finset_dec` autoparams normalize computed supports). CoqQ handles this
with `castlf` retyping (`dirac.v:1230-1691`). -/
theorem retypeWF (S' T' : Finset L) (d : Dirac D) {S T : Finset L}
    [h : WF d S T] (h₁ : S = S' := by finset_dec)
    (h₂ : T = T' := by finset_dec) : WF d S' T' :=
  ⟨h.wf.cast h₁ h₂⟩

/-! ## Leaf instances (D-10 constructor rows)

All leaves have distinct head symbols, so they never overlap: default
priority. -/

instance instWFOfBlock (f : LinM D S T) : WF (⌈f⌉ᴰ : Dirac D) S T :=
  ⟨wf_ofBlock f⟩

instance instWFKet (v : HS D S) : WF (∣v⟩ᴰ : Dirac D) ∅ S := ⟨wf_ket v⟩

instance instWFBra (v : HS D S) : WF (⟨v∣ᴰ : Dirac D) S ∅ := ⟨wf_bra v⟩

instance instWFNum (c : ℂ) : WF (num D c) ∅ ∅ := ⟨wf_num c⟩

instance instWFOne (S : Finset L) : WF (one D S : Dirac D) S S := ⟨wf_one⟩

instance instWFRingOne : WF (1 : Dirac D) ∅ ∅ :=
  ⟨by rw [one_def]; exact wf_num 1⟩

/-! ## Closure instances (D-10 operation rows)

Also keyed on distinct head symbols (`+`, `•`, …, `∘ᴰ`, `⊗ᴰ`, `*`, `·ᴰ`):
default priority throughout, so search order is driven purely by the term
structure. -/

instance instWFAdd (d e : Dirac D) [hd : WF d S T] [he : WF e S T] :
    WF (d + e) S T :=
  ⟨hd.wf.add he.wf⟩

instance instWFSMul (c : ℂ) (d : Dirac D) [h : WF d S T] : WF (c • d) S T :=
  ⟨h.wf.smul c⟩

instance instWFNeg (d : Dirac D) [h : WF d S T] : WF (-d) S T := ⟨h.wf.neg⟩

instance instWFSub (d e : Dirac D) [hd : WF d S T] [he : WF e S T] :
    WF (d - e) S T :=
  ⟨hd.wf.sub he.wf⟩

instance instWFAdj (d : Dirac D) [h : WF d S T] : WF (d†ᴰ) T S := ⟨h.wf.adj⟩

instance instWFConj (d : Dirac D) [h : WF d S T] : WF (dᶜᴰ) S T := ⟨h.wf.conj⟩

instance instWFTranspose (d : Dirac D) [h : WF d S T] : WF (dᵀᴰ) T S :=
  ⟨h.wf.transpose⟩

/-- The composition instance *unifies* the middle set: `d₁`'s source must
match `d₂`'s target syntactically. CoqQ: `muld_wf` as canonical
(`dirac.v:1522`). -/
instance instWFComp (d₁ d₂ : Dirac D) [h₁ : WF d₁ S T] [h₂ : WF d₂ W S] :
    WF (d₁ ∘ᴰ d₂) W T :=
  ⟨h₁.wf.comp h₂.wf⟩

instance instWFTensor (d₁ d₂ : Dirac D) [h₁ : WF d₁ S T] [h₂ : WF d₂ S' T'] :
    WF (d₁ ⊗ᴰ d₂) (S ∪ S') (T ∪ T') :=
  ⟨h₁.wf.tensor h₂.wf⟩

/-- `*` on `Dirac` *is* `⊗ᴰ` (D-4, `mul_def`); `ring`-normal forms use `*`,
so the tensor rule is keyed on both heads. -/
instance instWFMul (d₁ d₂ : Dirac D) [h₁ : WF d₁ S T] [h₂ : WF d₂ S' T'] :
    WF (d₁ * d₂) (S ∪ S') (T ∪ T') :=
  ⟨h₁.wf.tensor h₂.wf⟩

instance instWFDot (d₁ d₂ : Dirac D) [h₁ : WF d₁ S T] [h₂ : WF d₂ S' T'] :
    WF (d₁ ·ᴰ d₂) (S' ∪ (S \ T')) (T ∪ (T' \ S)) :=
  ⟨h₁.wf.dot h₂.wf⟩

/-! ## Big operators

Lower priority: their premises are `∀`-quantified (the most expensive search
step), and a failed `∑`/`∏` attempt should never delay the first-order
rules. -/

instance (priority := 500) instWFSum {ι : Type*} {s : Finset ι}
    {f : ι → Dirac D} [h : ∀ i, WF (f i) S T] : WF (∑ i ∈ s, f i) S T :=
  ⟨WFAt.sum fun i _ => (h i).wf⟩

/-- The big-tensor rule needs *function-valued* out-params `Sf`/`Tf`; higher-
order unification only assigns them when each factor's support is literally a
pattern in `j` (see the benchmark). CoqQ: `tends_wf` (`dirac.v:1573`). -/
instance (priority := 500) instWFProd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Sf Tf : ι → Finset L} {f : ι → Dirac D}
    [h : ∀ j, WF (f j) (Sf j) (Tf j)] :
    WF (∏ j, f j) (univ.biUnion Sf) (univ.biUnion Tf) :=
  ⟨WFAt.prod fun j => (h j).wf⟩

end Dirac

end Qhl
