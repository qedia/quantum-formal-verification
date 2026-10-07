import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.SDiff

/-!
# `finset_dec` — `Finset`-algebra side conditions

Replacement for CoqQ's 2097-line reflective tactic `setdec`
(`dirac/setdec.v`); Decision H3 (spec 02 §7). The side conditions of the
labelled laws (spec 03 §4, D-L1..D-L8) are quantifier-free facts about `∪`,
`∩`, `\`, `∅`, `⊆`, `=`, `Disjoint` over `Finset` variables. `grind` already
carries the membership theory: `Finset.mem_union`/`mem_inter`/`mem_sdiff`/
`notMem_empty` are `@[grind =]`, `Finset.ext` is `@[grind ext]`, and
`Finset.subset_iff` is `@[grind =]`. The one missing piece is the membership
characterization of `Disjoint`, passed as a parameter (hypotheses in context
are picked up by E-matching, so `Disjoint`-shaped assumptions are used too).

Benchmarked in `Qhl.Tactic.FinsetDecTest`.
-/

/-- Discharge a `Finset`-algebra side condition — `=`, `⊆` or `Disjoint`
between expressions built from `∪`, `∩`, `\`, `∅` and variables — possibly
from hypotheses of the same shape. CoqQ `setdec`; Decision H3 (spec 02 §7). -/
macro "finset_dec" : tactic => `(tactic| grind [Finset.disjoint_left])
