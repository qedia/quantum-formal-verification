import Qhl.Logic.Source.RulesSoundness

/-! # Ordinary classical variables for the source measurement axiom -/

namespace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]

/-- Derived single-outcome measurement on two distinct names, with all operand domains. -/
theorem SourceDerivPar.measureNamed {N : Type*} [DecidableEq N]
    {m k : ℕ} (x y : N) (hxy : x ≠ y)
    (r : RegExpr (N → Fin m) L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (A : SourceAssertion (N → Fin m) D)
    (hAy : A.FreshFor (SourceVariable.named y))
    (hdom : ∀ σ, A.classical ((SourceVariable.named x).set (σ y) σ) →
      A.defined ((SourceVariable.named x).set (σ y) σ) →
      ∀ i, A.defined ((SourceVariable.named x).set i σ)) :
    SourceDerivPar
      (A.measureOutcomePreSource r M (SourceVariable.named x).set
        (SourceVariable.named y).get)
      (.measure m k r M (SourceVariable.named x).set)
      (A.measureOutcomePostSource (SourceVariable.named x).get
        (SourceVariable.named y).get) :=
  SourceDerivPar.measure r M (SourceVariable.named x) (SourceVariable.named y)
    A (SourceVariable.independent_named hxy) hAy hdom

/-- Total-correctness single-outcome measurement with all operand domains. -/
theorem SourceDerivTot.measureNamed {N : Type*} [DecidableEq N]
    {m k : ℕ} (x y : N) (hxy : x ≠ y)
    (r : RegExpr (N → Fin m) L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (A : SourceAssertion (N → Fin m) D)
    (hAy : A.FreshFor (SourceVariable.named y))
    (hdom : ∀ σ, A.classical ((SourceVariable.named x).set (σ y) σ) →
      A.defined ((SourceVariable.named x).set (σ y) σ) →
      ∀ i, A.defined ((SourceVariable.named x).set i σ)) :
    SourceDerivTot
      (A.measureOutcomePreSource r M (SourceVariable.named x).set
        (SourceVariable.named y).get)
      (.measure m k r M (SourceVariable.named x).set)
      (A.measureOutcomePostSource (SourceVariable.named x).get
        (SourceVariable.named y).get) :=
  SourceDerivTot.measure r M (SourceVariable.named x) (SourceVariable.named y)
    A (SourceVariable.independent_named hxy) hAy hdom

/-- A fresh product ghost supplies independence; all operand domains are explicit. -/
theorem SourceDerivPar.measureWithGhost {m k : ℕ}
    (r : RegExpr (Fin m × Fin m) L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (A : SourceAssertion (Fin m) D)
    (hdom : ∀ j, A.classical j → A.defined j → ∀ i, A.defined i) :
    SourceDerivPar
      ((A.withGhost (Fin m)).measureOutcomePreSource r M SourceVariable.fst.set
        SourceVariable.snd.get)
      (.measure m k r M SourceVariable.fst.set)
      ((A.withGhost (Fin m)).measureOutcomePostSource SourceVariable.fst.get
        SourceVariable.snd.get) :=
  SourceDerivPar.measure r M SourceVariable.fst SourceVariable.snd
    (A.withGhost (Fin m)) SourceVariable.independent_fst_snd
    (SourceAssertion.withGhost_fresh A (Fin m)) (fun σ => hdom σ.2)

/-- Total-correctness measurement with a fresh product ghost. -/
theorem SourceDerivTot.measureWithGhost {m k : ℕ}
    (r : RegExpr (Fin m × Fin m) L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (A : SourceAssertion (Fin m) D)
    (hdom : ∀ j, A.classical j → A.defined j → ∀ i, A.defined i) :
    SourceDerivTot
      ((A.withGhost (Fin m)).measureOutcomePreSource r M SourceVariable.fst.set
        SourceVariable.snd.get)
      (.measure m k r M SourceVariable.fst.set)
      ((A.withGhost (Fin m)).measureOutcomePostSource SourceVariable.fst.get
        SourceVariable.snd.get) :=
  SourceDerivTot.measure r M SourceVariable.fst SourceVariable.snd
    (A.withGhost (Fin m)) SourceVariable.independent_fst_snd
    (SourceAssertion.withGhost_fresh A (Fin m)) (fun σ => hdom σ.2)

end Qhl
