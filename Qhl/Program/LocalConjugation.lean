import Qhl.Program.Step

/-! # Local conjugations commute with disjoint program primitives

These are state-level consequences of the explicit matrix frame lemmas
`liftSO_liftF_compl` and `liftSO_liftF_compr`. No commutation assumption is
required. Operators may be arbitrary, including nonunitary Kraus operators.
-/

namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]

omit [∀ i, Inhabited (D i)] in
/-- A local superoperator transports conjugation on disjoint cells. -/
theorem liftSO_conj_liftF {S T W : Finset L} (hd : Disjoint S T)
    (hS : S ⊆ W) (hT : T ⊆ W) (f : EndM D S)
    (E : SuperOp D T T) (x : EndM D W) :
    liftSO D hT E
        (liftF D hS f ∘ₗ x ∘ₗ LinearMap.adjoint (liftF D hS f)) =
      liftF D hS f ∘ₗ liftSO D hT E x ∘ₗ LinearMap.adjoint (liftF D hS f) := by
  rw [adjoint_liftF, liftSO_liftF_compl D hd hS hT,
    liftSO_liftF_compr D hd hS hT]

namespace PDensity

/-- State-level frame equality for any completely positive local map. -/
theorem mapSO_liftSO_conj {S T : Finset L} (hd : Disjoint S T)
    (f : EndM D S) (E : SuperOp D T T) (hE : IsCP D E) (ρ : PDensity D) :
    (ρ.conj (liftF D (subset_univ S) f)).mapSO
        (liftSO D (subset_univ T) E) (hE.liftSO D (subset_univ T)) =
      (ρ.mapSO (liftSO D (subset_univ T) E) (hE.liftSO D (subset_univ T))).conj
        (liftF D (subset_univ S) f) := by
  apply PDensity.ext
  exact liftSO_conj_liftF hd (subset_univ S) (subset_univ T) f E ρ.op

/-- Arbitrary operators on disjoint cell sets commute as state conjugations. -/
theorem conj_liftF_conj {S T : Finset L} (hd : Disjoint S T)
    (f : EndM D S) (g : EndM D T) (ρ : PDensity D) :
    (ρ.conj (liftF D (subset_univ S) f)).conj (liftF D (subset_univ T) g) =
      (ρ.conj (liftF D (subset_univ T) g)).conj (liftF D (subset_univ S) f) := by
  apply PDensity.ext
  have h := liftSO_conj_liftF hd (subset_univ S) (subset_univ T)
    f (formsoOf D g) ρ.op
  simpa only [liftSO_formsoOf, formsoOf_apply, conj_op] using h

/-- Gate and measurement-branch covariance for a disjoint local conjugation. -/
theorem conj_regLift_conj {S : Finset L} {k : ℕ} (r : Reg L k)
    (hd : Disjoint S r.sig) (f : EndM D S)
    (A : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun) (ρ : PDensity D) :
    (ρ.conj (liftF D (subset_univ S) f)).conj (regLift r A) =
      (ρ.conj (regLift r A)).conj (liftF D (subset_univ S) f) :=
  conj_liftF_conj hd f (r.op D A) ρ

/-- Initialization covariance for a disjoint local conjugation. -/
theorem mapSO_initLift_conj {S T : Finset L} (hd : Disjoint S T)
    (f : EndM D S) (ρ : PDensity D) :
    (ρ.conj (liftF D (subset_univ S) f)).mapSO (initLift T) (initLift_isQC T).1 =
      (ρ.mapSO (initLift T) (initLift_isQC T).1).conj (liftF D (subset_univ S) f) := by
  apply PDensity.ext
  exact liftSO_conj_liftF hd (subset_univ S) (subset_univ T) f (initSO D T) ρ.op

end PDensity

end Qhl
