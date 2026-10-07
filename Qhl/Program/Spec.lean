import Qhl.Program.Step

/-!
# P-4: step specification and mass accounting

Subgoal P-4 of spec 06 (master's `Spec/` discipline). All statements here are
**unconditional**: the unitarity of a gate and the completeness relation of a
measurement travel inside the syntax (Decision W5), so there is no lawfulness
hypothesis anywhere — master's `LawfulKernelContext` has no counterpart.

* branch counts per clause;
* a unitary step preserves mass, the measurement branches sum to the mass,
  initialisation preserves mass (`initLift_isQC`);
* the summary theorem `sum_mass_stepProg_le`: the total mass of the successors
  never exceeds the mass of the configuration (paper Prop 3.2 at the level of
  one step; the history-level statement is T-4).
-/

namespace Qhl

open Finset
open scoped NNReal

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {σT : Type*}

/-! ## Lifting unitaries and measurement families to the whole world -/

omit [Fintype L] in
theorem liftF_sum {S T : Finset L} {ι : Type*} (h : S ⊆ T) (s : Finset ι)
    (f : ι → EndM D S) : liftF D h (∑ i ∈ s, f i) = ∑ i ∈ s, liftF D h (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, liftF_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, liftF_add, ih]

theorem isUnitary_liftF {S T : Finset L} (h : S ⊆ T) {f : EndM D S} (hf : IsUnitary f) :
    IsUnitary (liftF D h f) := by
  constructor
  · rw [adjoint_liftF, ← liftF_comp, hf.1, liftF_one]
  · rw [adjoint_liftF, ← liftF_comp, hf.2, liftF_one]

theorem isQMeasure_liftF {S T : Finset L} {κ : Type*} [Fintype κ] (h : S ⊆ T)
    {f : κ → EndM D S} (hf : IsQMeasure D f) :
    IsQMeasure D fun i => liftF D h (f i) := by
  have hcomp : ∀ i, LinearMap.adjoint (liftF D h (f i)) ∘ₗ liftF D h (f i)
      = liftF D h (LinearMap.adjoint (f i) ∘ₗ f i) := fun i => by
    rw [adjoint_liftF, ← liftF_comp]
  change ∑ i, LinearMap.adjoint (liftF D h (f i)) ∘ₗ liftF D h (f i) = 1
  simp only [hcomp]
  rw [← liftF_sum, hf, liftF_one]

/-- The global operator of a gate on a register is unitary (R-3 + W6). -/
theorem isUnitary_regLift {k : ℕ} (r : Reg L k) (U : UnitaryOp (TSpace D r.toFun)) :
    IsUnitary (regLift r (U : TSpace D r.toFun →ₗ[ℂ] TSpace D r.toFun)) :=
  isUnitary_liftF _ (r.op_isUnitary U.2)

/-- The global operators of a measurement on a register form a measurement
family (G-4 + R-3 + W6). -/
theorem isQMeasure_regLift {m k : ℕ} (r : Reg L k) (Q : QMeasure m (TSpace D r.toFun)) :
    IsQMeasure D fun i => regLift r (Q.M i) :=
  isQMeasure_liftF _ (r.op_isQMeasure Q.complete)

/-! ## Trace bookkeeping -/

/-- Conjugation by a unitary preserves the trace. -/
theorem trace_conj_of_isUnitary {K : EndM D (univ : Finset L)} (hK : IsUnitary K)
    (x : EndM D (univ : Finset L)) :
    LinearMap.trace ℂ (HS D (univ : Finset L)) (K ∘ₗ x ∘ₗ LinearMap.adjoint K)
      = LinearMap.trace ℂ (HS D (univ : Finset L)) x := by
  have h := trace_kraussoOf D (fun _ : Unit => K) x
  rw [kraussoOf_apply, Fintype.sum_unique, Fintype.sum_unique, hK.1,
    Module.End.one_eq_id, LinearMap.comp_id] at h
  exact h

/-- The masses of the branches of a measurement family sum to the mass. -/
theorem sum_trace_conj_of_isQMeasure {κ : Type*} [Fintype κ]
    {K : κ → EndM D (univ : Finset L)} (hK : IsQMeasure D K)
    (x : EndM D (univ : Finset L)) :
    ∑ i, LinearMap.trace ℂ (HS D (univ : Finset L))
        (K i ∘ₗ x ∘ₗ LinearMap.adjoint (K i))
      = LinearMap.trace ℂ (HS D (univ : Finset L)) x := by
  have h := trace_kraussoOf D K x
  rw [kraussoOf_apply, map_sum, hK, Module.End.one_eq_id, LinearMap.comp_id] at h
  exact h

namespace PDensity

@[simp]
theorem mass_conj_of_isUnitary {K : EndM D (univ : Finset L)} (hK : IsUnitary K)
    (ρ : PDensity D) : (ρ.conj K).mass = ρ.mass := by
  refine NNReal.coe_injective ?_
  simp only [coe_mass, conj_op]
  rw [trace_conj_of_isUnitary hK]

theorem sum_mass_conj_of_isQMeasure {κ : Type*} [Fintype κ]
    {K : κ → EndM D (univ : Finset L)} (hK : IsQMeasure D K) (ρ : PDensity D) :
    ∑ i, (ρ.conj (K i)).mass = ρ.mass := by
  refine NNReal.coe_injective ?_
  push_cast
  simp only [coe_mass, conj_op]
  rw [← Complex.re_sum, sum_trace_conj_of_isQMeasure hK]

@[simp]
theorem mass_mapSO_of_isQC {E : SuperOp D (univ : Finset L) (univ : Finset L)}
    (hE : IsQC D E) (ρ : PDensity D) : (ρ.mapSO E hE.1).mass = ρ.mass := by
  refine NNReal.coe_injective ?_
  simp only [coe_mass, mapSO_op]
  rw [hE.2]

end PDensity

section Step

variable [∀ i, Inhabited (D i)]

/-! ## Branch counts (paper Prop 3.1(1)–(5)) -/

@[simp]
theorem length_stepProg_skip (σ : σT) (ρ : PDensity D) :
    (stepProg (.skip : Prog σT D) σ ρ).length = 1 := rfl

@[simp]
theorem length_stepProg_assign (f : σT → σT) (σ : σT) (ρ : PDensity D) :
    (stepProg (.assign f : Prog σT D) σ ρ).length = 1 := rfl

@[simp]
theorem length_stepProg_init (S : σT → Finset L) (σ : σT) (ρ : PDensity D) :
    (stepProg (.init S : Prog σT D) σ ρ).length = 1 := rfl

theorem length_stepProg_unitary {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (σ : σT) (ρ : PDensity D) :
    (stepProg (.unitary k r U) σ ρ).length = if r.dist σ then 1 else 0 := by
  by_cases h : r.dist σ
  · rw [stepProg_unitary r U σ ρ h, if_pos h, List.length_singleton]
  · rw [stepProg_unitary_of_not_dist r U σ ρ h, if_neg h, List.length_nil]

theorem length_stepProg_measure {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ))) (upd : Fin m → σT → σT) (σ : σT)
    (ρ : PDensity D) :
    (stepProg (.measure m k r M upd) σ ρ).length = if r.dist σ then m else 0 := by
  by_cases h : r.dist σ
  · rw [stepProg_measure r M upd σ ρ h, if_pos h, List.length_map, List.length_finRange]
  · rw [stepProg_measure_of_not_dist r M upd σ ρ h, if_neg h, List.length_nil]

/-! ## Mass accounting -/

/-- The total mass of the successors of a configuration. -/
noncomputable def stepMass (P : Prog σT D) (σ : σT) (ρ : PDensity D) : ℝ≥0 :=
  ((stepProg P σ ρ).map Config.mass).sum

@[simp]
theorem stepMass_skip (σ : σT) (ρ : PDensity D) :
    stepMass (.skip : Prog σT D) σ ρ = ρ.mass := by
  simp [stepMass, Config.mass]

@[simp]
theorem stepMass_assign (f : σT → σT) (σ : σT) (ρ : PDensity D) :
    stepMass (.assign f : Prog σT D) σ ρ = ρ.mass := by
  simp [stepMass, Config.mass]

/-- Initialisation preserves mass (`initLift_isQC`). -/
@[simp]
theorem stepMass_init (S : σT → Finset L) (σ : σT) (ρ : PDensity D) :
    stepMass (.init S : Prog σT D) σ ρ = ρ.mass := by
  simp only [stepMass, stepProg_init, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, Config.mass]
  exact PDensity.mass_mapSO_of_isQC (initLift_isQC (S σ)) ρ

/-- A unitary step preserves mass (W5: no side condition). -/
@[simp]
theorem stepMass_unitary {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (σ : σT) (ρ : PDensity D)
    (h : Function.Injective (r σ)) :
    stepMass (.unitary k r U) σ ρ = ρ.mass := by
  simp only [stepMass, stepProg_unitary r U σ ρ h, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, Config.mass]
  exact PDensity.mass_conj_of_isUnitary (isUnitary_regLift ⟨r σ, h⟩ (U σ)) ρ

/-- The measurement branches sum to the mass (W5: from `QMeasure.complete`). -/
theorem stepMass_measure {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ))) (upd : Fin m → σT → σT) (σ : σT)
    (ρ : PDensity D) (h : Function.Injective (r σ)) :
    stepMass (.measure m k r M upd) σ ρ = ρ.mass := by
  rw [stepMass, stepProg_measure r M upd σ ρ h, List.map_map]
  rw [show ((List.finRange m).map (Config.mass ∘ fun i =>
        (⟨.done, upd i σ, ρ.conj (regLift ⟨r σ, h⟩ ((M σ).M i))⟩ : Config σT D))).sum
      = ∑ i : Fin m, (ρ.conj (regLift ⟨r σ, h⟩ ((M σ).M i))).mass from by
    rw [Fin.sum_univ_def]
    rfl]
  exact PDensity.sum_mass_conj_of_isQMeasure
    (isQMeasure_regLift ⟨r σ, h⟩ (M σ)) ρ

/-- P-4 summary (paper Prop 3.2, one-step form): the successors of a
configuration carry at most its mass, with equality unless a register
expression is malformed. -/
theorem stepMass_le (P : Prog σT D) (σ : σT) (ρ : PDensity D) :
    stepMass P σ ρ ≤ ρ.mass := by
  induction P generalizing σ ρ with
  | skip => simp
  | assign f => simp
  | init S => simp
  | unitary k r U =>
      by_cases h : Function.Injective (r σ)
      · rw [stepMass_unitary r U σ ρ h]
      · simp [stepMass, stepProg_unitary_of_not_dist r U σ ρ h]
  | measure m k r M upd =>
      by_cases h : Function.Injective (r σ)
      · rw [stepMass_measure r M upd σ ρ h]
      · simp [stepMass, stepProg_measure_of_not_dist r M upd σ ρ h]
  | seq P₁ P₂ ih₁ _ =>
      rw [stepMass, stepProg_seq, List.map_map]
      exact le_of_le_of_eq (ih₁ σ ρ) rfl
  | ite b P₁ P₀ _ _ => simp [stepMass, Config.mass]
  | «while» b P _ =>
      by_cases h : b σ
      · simp [stepMass, stepProg_while_true b P σ ρ h, Config.mass]
      · simp [stepMass, stepProg_while_false b P σ ρ (by simpa using h), Config.mass]

end Step

end Qhl
