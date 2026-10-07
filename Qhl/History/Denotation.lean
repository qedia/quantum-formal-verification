import Qhl.History.Frontier

/-!
# T-3/T-4: the history denotation, its masses, and trace non-increase

Subgoals T-3 and T-4 of spec 06 (paper Def 3.4, eq (7)–(8), Prop 3.1–3.2;
master `NonterminationQuantityFromNext.lean:70`).

* `DenH P s` is the occurrence-indexed rendering of the paper's multiset
  `⟦P⟧(σ, ρ)` — the terminated histories of `P` from the cq-state `s`,
  indexed by the terminal cq-state they reach and by their length.
* `termMass root n` is the mass that terminates at depth exactly `n`;
  `terminatingTraceMass` sums it over all depths (paper eq (7)), and
  `NT` is the nontermination quantity (paper eq (8)).
* `terminatingTraceMass_le` is the paper's Prop 3.2: no mass is created.
* `termOpAt` is the per-classical-state aggregation `Θ(σ')` of eq (7),
  at a fixed depth.
-/

namespace Qhl

open Finset
open scoped NNReal ENNReal

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## List helpers -/

section ListLemmas

variable {α β M : Type*} [AddCommMonoid M]

theorem sum_map_flatMap (l : List α) (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem sum_map_filter_add_sum_map_filter_not (l : List α) (p : α → Bool) (g : α → M) :
    ((l.filter p).map g).sum + ((l.filter fun a => !p a).map g).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : p a = true
      · rw [List.filter_cons_of_pos h, List.filter_cons_of_neg (by simp [h])]
        simp only [List.map_cons, List.sum_cons]
        rw [add_assoc, ih]
      · rw [List.filter_cons_of_neg h, List.filter_cons_of_pos (by simp [h])]
        simp only [List.map_cons, List.sum_cons]
        rw [add_left_comm, ih]

omit [AddCommMonoid M] in
theorem map_filter_comp (l : List α) (f : α → β) (p : β → Bool) (g : β → M) :
    ((l.filter fun a => p (f a)).map fun a => g (f a)) = ((l.map f).filter p).map g := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p (f a) = true <;> simp [h, ih]

end ListLemmas

/-! ## T-3: the history denotation -/

/-- T-3: the occurrence-indexed rendering of the paper's multiset
`⟦P⟧(σ, ρ)` (Def 3.4): a terminal cq-state together with a terminated
history reaching it. -/
def DenH (P : Prog σT D) (s : CQState σT D) : Type _ :=
  Σ t : CQState σT D, Σ n : ℕ, HistFrom (Config.init P s) n (Config.term t)

/-! ## Masses of frontiers -/

/-- The total mass of the successors of a configuration. -/
noncomputable def cfgStepMass (c : Config σT D) : ℝ≥0 :=
  ((next c).map Config.mass).sum

@[simp]
theorem cfgStepMass_done (σ : σT) (ρ : PDensity D) :
    cfgStepMass (⟨.done, σ, ρ⟩ : Config σT D) = 0 := rfl

@[simp]
theorem cfgStepMass_running (P : Prog σT D) (σ : σT) (ρ : PDensity D) :
    cfgStepMass (⟨.running P, σ, ρ⟩ : Config σT D) = stepMass P σ ρ := rfl

/-- One step never creates mass (paper Prop 3.2, one-step form). -/
theorem cfgStepMass_le (c : Config σT D) : cfgStepMass c ≤ c.mass := by
  obtain ⟨ctrl, σ, ρ⟩ := c
  cases ctrl with
  | done => simp only [cfgStepMass_done]; exact zero_le
  | running P => exact stepMass_le P σ ρ

/-- The mass carried by the frontier at depth `n`. -/
noncomputable def frontMass (root : Config σT D) (n : ℕ) : ℝ≥0 :=
  ((boundedFront root n).map Config.mass).sum

@[simp]
theorem frontMass_zero (root : Config σT D) : frontMass root 0 = root.mass := by
  simp [frontMass, Config.mass]

theorem frontMass_succ (root : Config σT D) (n : ℕ) :
    frontMass root (n + 1) = ((boundedFront root n).map cfgStepMass).sum := by
  rw [frontMass, boundedFront_succ, sum_map_flatMap]
  rfl

@[simp]
theorem boundedFront_one (root : Config σT D) : boundedFront root 1 = next root := by
  simp [boundedFront]

/-- The mass that terminates at depth exactly `n`. -/
noncomputable def termMass (root : Config σT D) (n : ℕ) : ℝ≥0 :=
  (((boundedFront root n).filter fun c => c.isDone).map Config.mass).sum

/-- T-3: the terminal mass computed on the proof-relevant frontier agrees with
the one computed on the plain iteration. -/
theorem termMass_eq_terminalHistFront (root : Config σT D) (n : ℕ) :
    termMass root n = ((TerminalHistFront root n).map fun x => x.1.mass).sum := by
  rw [termMass, TerminalHistFront, ← histFront_map_fst]
  rw [map_filter_comp (HistFront root n) Sigma.fst (fun c => c.isDone) Config.mass]

/-- The key accounting step: what terminates at depth `n` plus what survives
to depth `n+1` is at most the mass at depth `n`. -/
theorem termMass_add_frontMass_succ_le (root : Config σT D) (n : ℕ) :
    termMass root n + frontMass root (n + 1) ≤ frontMass root n := by
  have key : ∀ l : List (Config σT D),
      ((l.filter fun c => c.isDone).map Config.mass).sum + (l.map cfgStepMass).sum
        ≤ (l.map Config.mass).sum := by
    intro l
    have hsplit := sum_map_filter_add_sum_map_filter_not l (fun c => c.isDone) Config.mass
    have hsplit2 := sum_map_filter_add_sum_map_filter_not l (fun c => c.isDone) cfgStepMass
    have hdone : ((l.filter fun c => c.isDone).map cfgStepMass).sum = 0 := by
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      have hcd : c.isDone = true := by simpa using List.of_mem_filter hc
      obtain ⟨ctrl, σ, ρ⟩ := c
      cases ctrl with
      | done => simp
      | running P => simp [Config.isDone] at hcd
    have hrun : ((l.filter fun c => !c.isDone).map cfgStepMass).sum
        ≤ ((l.filter fun c => !c.isDone).map Config.mass).sum :=
      List.sum_le_sum fun c _ => cfgStepMass_le c
    rw [← hsplit, ← hsplit2, hdone, zero_add]
    exact add_le_add le_rfl hrun
  rw [frontMass_succ]
  simp only [termMass, frontMass]
  exact key (boundedFront root n)

/-- Partial sums of terminal masses, plus the surviving mass, stay below the
initial mass. -/
theorem sum_termMass_add_frontMass_le (root : Config σT D) (n : ℕ) :
    ∑ i ∈ Finset.range n, termMass root i + frontMass root n ≤ root.mass := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, add_assoc]
      exact le_trans (add_le_add le_rfl (termMass_add_frontMass_succ_le root n)) ih

theorem sum_termMass_le (root : Config σT D) (n : ℕ) :
    ∑ i ∈ Finset.range n, termMass root i ≤ root.mass :=
  le_trans (le_add_of_nonneg_right zero_le) (sum_termMass_add_frontMass_le root n)

/-! ## T-3: the terminating mass and the nontermination quantity -/

/-- The total terminating mass of a configuration (paper eq (7)). -/
noncomputable def terminatingTraceMass (root : Config σT D) : ℝ≥0∞ :=
  ∑' n, (termMass root n : ℝ≥0∞)

/-- T-4 (paper Prop 3.2): a program never creates mass. -/
theorem terminatingTraceMass_le (root : Config σT D) :
    terminatingTraceMass root ≤ (root.mass : ℝ≥0∞) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_le_coe]
  exact sum_termMass_le root n

/-- The nontermination quantity of a configuration (paper eq (8)). -/
noncomputable def NT (root : Config σT D) : ℝ≥0∞ :=
  (root.mass : ℝ≥0∞) - terminatingTraceMass root

theorem terminatingTraceMass_add_NT (root : Config σT D) :
    terminatingTraceMass root + NT root = (root.mass : ℝ≥0∞) :=
  add_tsub_cancel_of_le (terminatingTraceMass_le root)

/-! ## T-4: the structural clauses of paper Prop 3.1 (loop-free fragment)

Each clause describes the frontier at depth one of a program run, i.e. the
image of Table 2's rule for that construct. -/

@[simp]
theorem boundedFront_skip (s : CQState σT D) :
    boundedFront (Config.init .skip s) 1 = [Config.term s] := by
  simp [Config.init, Config.term]

@[simp]
theorem boundedFront_assign (f : σT → σT) (s : CQState σT D) :
    boundedFront (Config.init (.assign f) s) 1 = [Config.term ⟨f s.cls, s.q⟩] := by
  simp [Config.init, Config.term]

theorem boundedFront_initProg (S : σT → Finset L) (s : CQState σT D) :
    boundedFront (Config.init (.init S) s) 1 =
      [Config.term ⟨s.cls, s.q.mapSO (initLift (S s.cls)) (initLift_isQC (S s.cls)).1⟩] := by
  simp [Config.init, Config.term]

theorem boundedFront_unitary {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (s : CQState σT D)
    (h : Function.Injective (r s.cls)) :
    boundedFront (Config.init (.unitary k r U) s) 1 =
      [Config.term ⟨s.cls, s.q.conj (regLift ⟨r s.cls, h⟩ (U s.cls))⟩] := by
  rw [boundedFront_one, Config.init, next_running, stepProg_unitary r U s.cls s.q h]
  rfl

theorem boundedFront_unitary_of_not_dist {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (s : CQState σT D)
    (h : ¬ Function.Injective (r s.cls)) :
    boundedFront (Config.init (.unitary k r U) s) 1 = [] := by
  rw [boundedFront_one, Config.init, next_running,
    stepProg_unitary_of_not_dist r U s.cls s.q h]

theorem boundedFront_measure {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ))) (upd : Fin m → σT → σT)
    (s : CQState σT D) (h : Function.Injective (r s.cls)) :
    boundedFront (Config.init (.measure m k r M upd) s) 1 =
      (List.finRange m).map fun i =>
        Config.term ⟨upd i s.cls, s.q.conj (regLift ⟨r s.cls, h⟩ ((M s.cls).M i))⟩ := by
  rw [boundedFront_one, Config.init, next_running, stepProg_measure r M upd s.cls s.q h]
  rfl

theorem boundedFront_seq (P₁ P₂ : Prog σT D) (s : CQState σT D) :
    boundedFront (Config.init (.seq P₁ P₂) s) 1 =
      (boundedFront (Config.init P₁ s) 1).map fun c => ⟨c.ctrl.seqWith P₂, c.cls, c.q⟩ := by
  simp [Config.init]

@[simp]
theorem boundedFront_ite (b : σT → Bool) (P₁ P₀ : Prog σT D) (s : CQState σT D) :
    boundedFront (Config.init (.ite b P₁ P₀) s) 1 =
      [Config.init (if b s.cls then P₁ else P₀) s] := by
  simp [Config.init]

theorem boundedFront_while_true (b : σT → Bool) (P : Prog σT D) (s : CQState σT D)
    (h : b s.cls = true) :
    boundedFront (Config.init (.while b P) s) 1 =
      [Config.init (.seq P (.while b P)) s] := by
  rw [boundedFront_one, Config.init, next_running, stepProg_while_true b P s.cls s.q h]
  rfl

theorem boundedFront_while_false (b : σT → Bool) (P : Prog σT D) (s : CQState σT D)
    (h : b s.cls = false) :
    boundedFront (Config.init (.while b P) s) 1 = [Config.term s] := by
  rw [boundedFront_one, Config.init, next_running, stepProg_while_false b P s.cls s.q h]
  rfl

/-! ## T-4: aggregation by terminal classical state (paper eq (7)) -/

section Aggregate

variable [DecidableEq σT]

/-- The paper's `Θ(σ')` at a fixed depth: the sum of the terminal quantum
states whose classical component is `σ'`. -/
noncomputable def termOpAt (root : Config σT D) (n : ℕ) (σ' : σT) :
    EndM D (univ : Finset L) :=
  (((boundedFront root n).filter fun c => c.isDone && decide (c.cls = σ')).map
    fun c => c.q.op).sum

theorem termOpAt_isPositive (root : Config σT D) (n : ℕ) (σ' : σT) :
    (termOpAt root n σ').IsPositive := by
  rw [termOpAt]
  generalize ((boundedFront root n).filter fun c => c.isDone && decide (c.cls = σ')) = l
  induction l with
  | nil => simp
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact c.q.pos.add ih

/-- The finite-horizon aggregation of `Θ(σ')` over the first `N` depths. -/
noncomputable def termOpUpTo (root : Config σT D) (N : ℕ) (σ' : σT) :
    EndM D (univ : Finset L) :=
  ∑ n ∈ Finset.range N, termOpAt root n σ'

theorem termOpUpTo_isPositive (root : Config σT D) (N : ℕ) (σ' : σT) :
    (termOpUpTo root N σ').IsPositive := by
  rw [termOpUpTo]
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact ih.add (termOpAt_isPositive root N σ')

end Aggregate

end Qhl
