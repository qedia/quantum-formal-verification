import Qhl.Logic.Source.MeasurementAll
import Qhl.Logic.Source.Convex
import Qhl.Logic.Source.LoopGhost
import Qhl.Logic.Source.Variable
import Qhl.Logic.Source.Accumulation
import Qhl.Logic.Source.AccumulationDomain

/-! # Hoare derivations with the source rule premises

Accum2 requires every postpredicate to be defined whenever the common classical
postcondition holds. Both accumulation rules retain equality normalization of
the input family; Accum1 permits a contractive singleton output.
No constructor reflects semantic validity into a derivation or
imports a backend derivation.
The classical formulas and quantum predicates are interpreted shallowly in a
finite quantum world. Generic operational frame premises can be broader than the
source's syntactic conditions; RegisterAccumulation supplies the source-shaped
register locality and unchanged-parameter interface.
Initialization retains the existing finite-block reset convention.
Initialization.lean proves the printed singleton formula and exact correspondence
with singleton-reset macros, including state-dependent finite blocks.
The scalar Convex rules are represented explicitly: Convex1 has a nonempty
index family, whereas Convex2 includes the empty family.
-/

namespace Qhl

open scoped NNReal

universe u

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type u}

namespace SourceAssertion

/-- The source initialization precondition retains the classical condition and domain. -/
noncomputable def initPreSource (A : SourceAssertion σT D) (S : σT → Finset L) :
    SourceAssertion σT D where
  classical := A.classical
  defined := A.defined
  quantum := A.quantum.initPre S

/-- The source unitary precondition requires a distinct register and a defined postpredicate. -/
noncomputable def unitaryPreSource (A : SourceAssertion σT D) {k : ℕ}
    (r : RegExpr σT L k) (U : ∀ σ, UnitaryOp (TSpace D (r σ))) :
    SourceAssertion σT D where
  classical := A.classical
  defined σ := Function.Injective (r σ) ∧ A.defined σ
  quantum := A.quantum.unitaryPre r U

end SourceAssertion

/-- Source partial derivations, with the post-definedness correction to Accum2. -/
inductive SourceDerivPar : SourceAssertion σT D → Prog σT D →
    SourceAssertion σT D → Prop where
  /-- Skip preserves the source assertion. -/
  | skip (A : SourceAssertion σT D) : SourceDerivPar A .skip A
  /-- Assignment substitutes throughout the source assertion. -/
  | assign (f : σT → σT) (A : SourceAssertion σT D) :
      SourceDerivPar (A.subst f) (.assign f) A
  /-- Quantum initialization, retaining the finite-block convention. -/
  | initProg (S : σT → Finset L) (A : SourceAssertion σT D) :
      SourceDerivPar (A.initPreSource S) (.init S) A
  /-- A unitary applied to a distinct register. -/
  | unitary {k : ℕ} (r : RegExpr σT L k)
      (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (A : SourceAssertion σT D) :
      SourceDerivPar (A.unitaryPreSource r U) (.unitary k r U) A
  /-- All-outcome measurement with strict definedness of every operand. -/
  | measureAll {m k : ℕ} (r : RegExpr σT L k)
      (M : ∀ σ, QMeasure m (TSpace D (r σ)))
      (x : SourceVariable σT (Fin m)) (A : SourceAssertion σT D) :
      SourceDerivPar (A.measureAllPreSource r M x.set)
        (.measure m k r M x.set) A
  /-- Move a strict quantum mask to the classical postcondition. -/
  | mask {A B : SourceAssertion σT D} {P : Prog σT D} (b : σT → Prop) :
      SourceDerivPar A P (B.quantumMask b) →
      SourceDerivPar A P
        (B.withClassical fun σ => B.classical σ ∧ b σ)
  /-- Sequential composition. -/
  | seq {A B C : SourceAssertion σT D} {P₁ P₂ : Prog σT D} :
      SourceDerivPar A P₁ B → SourceDerivPar B P₂ C →
      SourceDerivPar A (.seq P₁ P₂) C
  /-- A classical guard selects one of two proofs with the same source precondition. -/
  | cond {A B : SourceAssertion σT D} {P₁ P₀ : Prog σT D} (b : σT → Bool) :
      SourceDerivPar (A.withClassical fun σ => A.classical σ ∧ b σ = true) P₁ B →
      SourceDerivPar (A.withClassical fun σ => A.classical σ ∧ b σ = false) P₀ B →
      SourceDerivPar A (.ite b P₁ P₀) B
  /-- Partial-correctness loop with source invariant. -/
  | whileLoop {A : SourceAssertion σT D} {P : Prog σT D} (b : σT → Bool) :
      SourceDerivPar (A.withClassical fun σ => A.classical σ ∧ b σ = true) P A →
      SourceDerivPar A (.while b P)
        (A.withClassical fun σ => A.classical σ ∧ b σ = false)
  /-- Consequence requires source entailment, including domain agreement. -/
  | conseq {A A' B' B : SourceAssertion σT D} {P : Prog σT D} :
      SourceAssertion.Entails A A' → SourceDerivPar A' P B' →
      SourceAssertion.Entails B' B → SourceDerivPar A P B
  /-- Source Kraus accumulation with an operationally framed program and
  postpredicates defined under the common classical postcondition. -/
  | accum2 {ι : Type} [Fintype ι] (φ ψ : σT → Prop)
      (A B : ι → SourceAssertion σT D)
      (K : σT → ι → EndM D (Finset.univ : Finset L))
      (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
      (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
      (hdom : ∀ σ, ψ σ → ∀ i, (B i).defined σ) :
      (∀ i, SourceDerivPar ((A i).withClassical φ) P ((B i).withClassical ψ)) →
      SourceDerivPar (SourceAssertion.kraus φ A K hK) P
        (SourceAssertion.kraus ψ B K hK)
  /-- Source Accum1 merges exclusive classical outcomes under Kraus domination. -/
  | accum1 {ι : Type} [Fintype ι] (φ : σT → Prop) (ψ : ι → σT → Prop)
      (A : ι → SourceAssertion σT D) (B : SourceAssertion σT D)
      (K : σT → ι → EndM D (Finset.univ : Finset L))
      (J : σT → EndM D (Finset.univ : Finset L))
      (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
      (hJ : ∀ σ, LinearMap.adjoint (J σ) ∘ₗ J σ ≤ 1)
      (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
      (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
      (hdom : ∀ σ i (ρ : PDensity D), (ρ.conj (K σ i)).op ≤ (ρ.conj (J σ)).op) :
      (∀ i, SourceDerivPar ((A i).withClassical φ) P (B.withClassical (ψ i))) →
      SourceDerivPar (SourceAssertion.kraus φ A K hK) P
        (SourceAssertion.krausOne (fun σ => ∃ i, ψ i σ) B J hJ)
  /-- Accum2 retaining a preserved operand domain in both quantum predicates,
  with every postpredicate defined under the common classical postcondition. -/
  | accum2Domain {ι : Type} [Fintype ι] (φ ψ : σT → Prop)
      (A B : ι → SourceAssertion σT D)
      (K : σT → ι → EndM D (Finset.univ : Finset L))
      (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
      (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
      (d : σT → Prop) (hd : P.PreservesParameters d)
      (hdom : ∀ σ, ψ σ → ∀ i, (B i).defined σ) :
      (∀ i, SourceDerivPar ((A i).withClassical φ) P ((B i).withClassical ψ)) →
      SourceDerivPar ((SourceAssertion.kraus φ A K hK).onDomain d) P
        ((SourceAssertion.kraus ψ B K hK).onDomain d)
  /-- Accum1 retaining a preserved operand domain in both quantum predicates. -/
  | accum1Domain {ι : Type} [Fintype ι] (φ : σT → Prop) (ψ : ι → σT → Prop)
      (A : ι → SourceAssertion σT D) (B : SourceAssertion σT D)
      (K : σT → ι → EndM D (Finset.univ : Finset L))
      (J : σT → EndM D (Finset.univ : Finset L))
      (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
      (hJ : ∀ σ, LinearMap.adjoint (J σ) ∘ₗ J σ ≤ 1)
      (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
      (d : σT → Prop) (hd : P.PreservesParameters d)
      (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
      (hdom : ∀ σ i (ρ : PDensity D), (ρ.conj (K σ i)).op ≤ (ρ.conj (J σ)).op) :
      (∀ i, SourceDerivPar ((A i).withClassical φ) P (B.withClassical (ψ i))) →
      SourceDerivPar ((SourceAssertion.kraus φ A K hK).onDomain d) P
        ((SourceAssertion.krausOne (fun σ => ∃ i, ψ i σ) B J hJ).onDomain d)
  /-- Scalar Convex1 with a genuine maximum over a nonempty family. -/
  | convex1 {ι : Type} [Fintype ι] [Nonempty ι]
      (φ : σT → Prop) (ψ : ι → σT → Prop)
      (A : ι → SourceAssertion σT D) (B : SourceAssertion σT D)
      (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1) (P : Prog σT D)
      (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ) :
      (∀ i, SourceDerivPar ((A i).withClassical φ) P (B.withClassical (ψ i))) →
      SourceDerivPar (SourceAssertion.convex φ A p hp) P
        (SourceAssertion.scaled (fun σ => ∃ i, ψ i σ) B
          (SourceAssertion.convexMax p) (SourceAssertion.convexMax_le_one p hp))
  /-- Scalar Convex2 includes the empty family and retains strict post-definedness. -/
  | convex2 {ι : Type} [Fintype ι] (φ ψ : σT → Prop)
      (A B : ι → SourceAssertion σT D)
      (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1) (P : Prog σT D)
      (hdom : ∀ σ, ψ σ → ∀ i, (B i).defined σ) :
      (∀ i, SourceDerivPar ((A i).withClassical φ) P ((B i).withClassical ψ)) →
      SourceDerivPar (SourceAssertion.convex φ A p hp) P
        (SourceAssertion.convex ψ B p hp)

/-- Source total derivations, with the post-definedness correction to Accum2. -/
inductive SourceDerivTot : {σT : Type u} → SourceAssertion σT D → Prog σT D →
    SourceAssertion σT D → Prop where
  /-- Skip preserves the source assertion. -/
  | skip {σT : Type u} (A : SourceAssertion σT D) : SourceDerivTot A .skip A
  /-- Assignment substitutes throughout the source assertion. -/
  | assign {σT : Type u} (f : σT → σT) (A : SourceAssertion σT D) :
      SourceDerivTot (A.subst f) (.assign f) A
  /-- Quantum initialization, retaining the finite-block convention. -/
  | initProg {σT : Type u} (S : σT → Finset L) (A : SourceAssertion σT D) :
      SourceDerivTot (A.initPreSource S) (.init S) A
  /-- A unitary applied to a distinct register. -/
  | unitary {σT : Type u} {k : ℕ} (r : RegExpr σT L k)
      (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (A : SourceAssertion σT D) :
      SourceDerivTot (A.unitaryPreSource r U) (.unitary k r U) A
  /-- All-outcome measurement with strict definedness of every operand. -/
  | measureAll {σT : Type u} {m k : ℕ} (r : RegExpr σT L k)
      (M : ∀ σ, QMeasure m (TSpace D (r σ)))
      (x : SourceVariable σT (Fin m)) (A : SourceAssertion σT D) :
      SourceDerivTot (A.measureAllPreSource r M x.set)
        (.measure m k r M x.set) A
  /-- Move a strict quantum mask to the classical postcondition. -/
  | mask {σT : Type u} {A B : SourceAssertion σT D} {P : Prog σT D} (b : σT → Prop) :
      SourceDerivTot A P (B.quantumMask b) →
      SourceDerivTot A P
        (B.withClassical fun σ => B.classical σ ∧ b σ)
  /-- Sequential composition. -/
  | seq {σT : Type u} {A B C : SourceAssertion σT D} {P₁ P₂ : Prog σT D} :
      SourceDerivTot A P₁ B → SourceDerivTot B P₂ C →
      SourceDerivTot A (.seq P₁ P₂) C
  /-- A classical guard selects one of two proofs with the same source precondition. -/
  | cond {σT : Type u} {A B : SourceAssertion σT D} {P₁ P₀ : Prog σT D} (b : σT → Bool) :
      SourceDerivTot (A.withClassical fun σ => A.classical σ ∧ b σ = true) P₁ B →
      SourceDerivTot (A.withClassical fun σ => A.classical σ ∧ b σ = false) P₀ B →
      SourceDerivTot A (.ite b P₁ P₀) B
  /-- The paper's independent identity-predicate integer ranking rule. -/
  | whileLoop {σT : Type u} {A : SourceAssertion σT D} {P : Prog σT D} (b : σT → Bool)
      (t : σT → Int) (hbound : ∀ σ, A.classical σ → 0 ≤ t σ) :
      SourceDerivTot (A.withClassical fun σ => A.classical σ ∧ b σ = true) P A →
      (∀ z : Int, SourceDerivTot
        (SourceAssertion.identity (D := D)
          (fun σ => A.classical σ ∧ b σ = true ∧ t σ = z)) P
        (SourceAssertion.identity (D := D) (fun σ => t σ < z))) →
      SourceDerivTot A (.while b P)
        (A.withClassical fun σ => A.classical σ ∧ b σ = false)
  /-- The same total-loop rule with its fresh integer variable represented explicitly. -/
  | whileLoopGhost {σT : Type u} {A : SourceAssertion σT D} {P : Prog σT D} (b : σT → Bool)
      (t : σT → Int) (hbound : ∀ σ, A.classical σ → 0 ≤ t σ) :
      SourceDerivTot (A.withClassical fun σ => A.classical σ ∧ b σ = true) P A →
      SourceDerivTot (A.rankGhostPre b t)
        (P.mapStore (StoreLens.fst (R := Int))) (SourceAssertion.rankGhostPost t) →
      SourceDerivTot A (.while b P)
        (A.withClassical fun σ => A.classical σ ∧ b σ = false)
  /-- Consequence requires source entailment, including domain agreement. -/
  | conseq {σT : Type u} {A A' B' B : SourceAssertion σT D} {P : Prog σT D} :
      SourceAssertion.Entails A A' → SourceDerivTot A' P B' →
      SourceAssertion.Entails B' B → SourceDerivTot A P B
  /-- Source Kraus accumulation with an operationally framed program and
  postpredicates defined under the common classical postcondition. -/
  | accum2 {σT : Type u} {ι : Type} [Fintype ι] (φ ψ : σT → Prop)
      (A B : ι → SourceAssertion σT D)
      (K : σT → ι → EndM D (Finset.univ : Finset L))
      (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
      (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
      (hdom : ∀ σ, ψ σ → ∀ i, (B i).defined σ) :
      (∀ i, SourceDerivTot ((A i).withClassical φ) P ((B i).withClassical ψ)) →
      SourceDerivTot (SourceAssertion.kraus φ A K hK) P
        (SourceAssertion.kraus ψ B K hK)
  /-- Source Accum1 merges exclusive classical outcomes under Kraus domination. -/
  | accum1 {σT : Type u} {ι : Type} [Fintype ι] (φ : σT → Prop) (ψ : ι → σT → Prop)
      (A : ι → SourceAssertion σT D) (B : SourceAssertion σT D)
      (K : σT → ι → EndM D (Finset.univ : Finset L))
      (J : σT → EndM D (Finset.univ : Finset L))
      (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
      (hJ : ∀ σ, LinearMap.adjoint (J σ) ∘ₗ J σ ≤ 1)
      (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
      (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
      (hdom : ∀ σ i (ρ : PDensity D), (ρ.conj (K σ i)).op ≤ (ρ.conj (J σ)).op) :
      (∀ i, SourceDerivTot ((A i).withClassical φ) P (B.withClassical (ψ i))) →
      SourceDerivTot (SourceAssertion.kraus φ A K hK) P
        (SourceAssertion.krausOne (fun σ => ∃ i, ψ i σ) B J hJ)
  /-- Accum2 retaining a preserved operand domain in both quantum predicates,
  with every postpredicate defined under the common classical postcondition. -/
  | accum2Domain {σT : Type u} {ι : Type} [Fintype ι] (φ ψ : σT → Prop)
      (A B : ι → SourceAssertion σT D)
      (K : σT → ι → EndM D (Finset.univ : Finset L))
      (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
      (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
      (d : σT → Prop) (hd : P.PreservesParameters d)
      (hdom : ∀ σ, ψ σ → ∀ i, (B i).defined σ) :
      (∀ i, SourceDerivTot ((A i).withClassical φ) P ((B i).withClassical ψ)) →
      SourceDerivTot ((SourceAssertion.kraus φ A K hK).onDomain d) P
        ((SourceAssertion.kraus ψ B K hK).onDomain d)
  /-- Accum1 retaining a preserved operand domain in both quantum predicates. -/
  | accum1Domain {σT : Type u} {ι : Type} [Fintype ι] (φ : σT → Prop) (ψ : ι → σT → Prop)
      (A : ι → SourceAssertion σT D) (B : SourceAssertion σT D)
      (K : σT → ι → EndM D (Finset.univ : Finset L))
      (J : σT → EndM D (Finset.univ : Finset L))
      (hK : ∀ σ, ∑ i, LinearMap.adjoint (K σ i) ∘ₗ K σ i = 1)
      (hJ : ∀ σ, LinearMap.adjoint (J σ) ∘ₗ J σ ≤ 1)
      (P : Prog σT D) (hframe : ∀ i, P.KrausFrame (fun σ => K σ i))
      (d : σT → Prop) (hd : P.PreservesParameters d)
      (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
      (hdom : ∀ σ i (ρ : PDensity D), (ρ.conj (K σ i)).op ≤ (ρ.conj (J σ)).op) :
      (∀ i, SourceDerivTot ((A i).withClassical φ) P (B.withClassical (ψ i))) →
      SourceDerivTot ((SourceAssertion.kraus φ A K hK).onDomain d) P
        ((SourceAssertion.krausOne (fun σ => ∃ i, ψ i σ) B J hJ).onDomain d)
  /-- Scalar Convex1 with a genuine maximum over a nonempty family. -/
  | convex1 {σT : Type u} {ι : Type} [Fintype ι] [Nonempty ι]
      (φ : σT → Prop) (ψ : ι → σT → Prop)
      (A : ι → SourceAssertion σT D) (B : SourceAssertion σT D)
      (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1) (P : Prog σT D)
      (hexcl : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ) :
      (∀ i, SourceDerivTot ((A i).withClassical φ) P (B.withClassical (ψ i))) →
      SourceDerivTot (SourceAssertion.convex φ A p hp) P
        (SourceAssertion.scaled (fun σ => ∃ i, ψ i σ) B
          (SourceAssertion.convexMax p) (SourceAssertion.convexMax_le_one p hp))
  /-- Scalar Convex2 includes the empty family and retains strict post-definedness. -/
  | convex2 {σT : Type u} {ι : Type} [Fintype ι] (φ ψ : σT → Prop)
      (A B : ι → SourceAssertion σT D)
      (p : ι → ℝ≥0) (hp : ∑ i, p i ≤ 1) (P : Prog σT D)
      (hdom : ∀ σ, ψ σ → ∀ i, (B i).defined σ) :
      (∀ i, SourceDerivTot ((A i).withClassical φ) P ((B i).withClassical ψ)) →
      SourceDerivTot (SourceAssertion.convex φ A p hp) P
        (SourceAssertion.convex ψ B p hp)

/-- Selected outcomes are derived using all-outcome measurement and Rule-Mask.
The omitted operands must remain defined because quantum masking is strict. -/
theorem SourceDerivPar.measureSelected {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (x : SourceVariable σT (Fin m)) (S : σT → Fin m → Bool)
    (A : SourceAssertion σT D) (hS : ∀ i σ, S (x.set i σ) = S σ)
    (hdom : ∀ σ, (A.measureSelectedPreSource r M x.set S).classical σ →
      (∀ i, S σ i = true → A.defined (x.set i σ)) → ∀ i, A.defined (x.set i σ)) :
    SourceDerivPar (A.measureSelectedPreSource r M x.set S)
      (.measure m k r M x.set) (A.measureSelectedPostSource x.get S) := by
  apply SourceDerivPar.conseq
    (SourceAssertion.measureSelectedPreSource_all A r M x S hS hdom)
  · exact .mask _ (.measureAll r M x (A.measureSelectionOperand x.get S))
  · exact SourceAssertion.measureSelectionOperand_post A x.get S

/-- Selected outcomes are derived using all-outcome measurement and Rule-Mask.
The omitted operands must remain defined because quantum masking is strict. -/
theorem SourceDerivTot.measureSelected {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (x : SourceVariable σT (Fin m)) (S : σT → Fin m → Bool)
    (A : SourceAssertion σT D) (hS : ∀ i σ, S (x.set i σ) = S σ)
    (hdom : ∀ σ, (A.measureSelectedPreSource r M x.set S).classical σ →
      (∀ i, S σ i = true → A.defined (x.set i σ)) → ∀ i, A.defined (x.set i σ)) :
    SourceDerivTot (A.measureSelectedPreSource r M x.set S)
      (.measure m k r M x.set) (A.measureSelectedPostSource x.get S) := by
  apply SourceDerivTot.conseq
    (SourceAssertion.measureSelectedPreSource_all A r M x S hS hdom)
  · exact .mask _ (.measureAll r M x (A.measureSelectionOperand x.get S))
  · exact SourceAssertion.measureSelectionOperand_post A x.get S

/-- The original single-outcome rule is a derived singleton-selection rule.
The freshness argument is retained for compatibility with the printed source rule;
the additional premise supplies definedness of every substituted operand. -/
theorem SourceDerivPar.measure {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (x y : SourceVariable σT (Fin m)) (A : SourceAssertion σT D)
    (hxy : SourceVariable.Independent x y) (_hAy : A.FreshFor y)
    (hdom : ∀ σ, A.classical (x.set (y.get σ) σ) →
      A.defined (x.set (y.get σ) σ) → ∀ i, A.defined (x.set i σ)) :
    SourceDerivPar (A.measureOutcomePreSource r M x.set y.get)
      (.measure m k r M x.set) (A.measureOutcomePostSource x.get y.get) := by
  apply SourceDerivPar.conseq
    (SourceAssertion.measureSelectedPreSource_singleton A r M x.set y.get).1
  · apply SourceDerivPar.measureSelected r M x (fun σ i => decide (i = y.get σ)) A
    · intro i σ
      funext j
      rw [hxy.1]
    · intro σ hc hd
      exact hdom σ (hc (y.get σ) (by simp)) (hd (y.get σ) (by simp))
  · exact (SourceAssertion.measureSelectedPostSource_singleton A x.get y.get).1

/-- The original single-outcome rule is a derived singleton-selection rule.
The freshness argument is retained for compatibility with the printed source rule;
the additional premise supplies definedness of every substituted operand. -/
theorem SourceDerivTot.measure {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (x y : SourceVariable σT (Fin m)) (A : SourceAssertion σT D)
    (hxy : SourceVariable.Independent x y) (_hAy : A.FreshFor y)
    (hdom : ∀ σ, A.classical (x.set (y.get σ) σ) →
      A.defined (x.set (y.get σ) σ) → ∀ i, A.defined (x.set i σ)) :
    SourceDerivTot (A.measureOutcomePreSource r M x.set y.get)
      (.measure m k r M x.set) (A.measureOutcomePostSource x.get y.get) := by
  apply SourceDerivTot.conseq
    (SourceAssertion.measureSelectedPreSource_singleton A r M x.set y.get).1
  · apply SourceDerivTot.measureSelected r M x (fun σ i => decide (i = y.get σ)) A
    · intro i σ
      funext j
      rw [hxy.1]
    · intro σ hc hd
      exact hdom σ (hc (y.get σ) (by simp)) (hd (y.get σ) (by simp))
  · exact (SourceAssertion.measureSelectedPostSource_singleton A x.get y.get).1

end Qhl
