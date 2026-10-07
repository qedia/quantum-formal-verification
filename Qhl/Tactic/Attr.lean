import Mathlib.Init

/-!
# Simp sets for the Qhl development

Registered here because an attribute cannot be used in the file that declares it.
-/

/-- Componentwise computation lemmas on `HS` (`toLp`/`ofLp`/`cdv`/`deltav`);
spec 02, subgoal H-3. -/
register_simp_attr HS_simps

/-- Cast lemmas for `castH`/`castF`; spec 02, subgoal H-9. -/
register_simp_attr cast_simps

/-- Blockwise computations on the `Dirac` type; spec 03 §8. -/
register_simp_attr dirac_simps

/-- Support-computation table for `Dirac.WFAt`; spec 03, subgoal D-10. -/
register_simp_attr wf_simps
