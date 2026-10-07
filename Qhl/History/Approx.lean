import Qhl.History.Correctness

/-!
# S-1: ENNReal frontier sums and the bounded value functional

Subgoal S-1 of spec 07 (design decisions V4/V6; the step-indexed rendering of
paper arXiv:2412.09869 A.2's Claim (37) and of master's additive discipline,
`HistoryTraceDecrease.lean:85`).

* `dSum h c n` sums a terminal weight `h` over the terminated part of the
  frontier at depth `n`; `postAtE`/`termMassE` are its two instances
  (expectation of an effect family, mass). Everything is `ℝ≥0∞`-valued so
  the soundness algebra never leaves a complete lattice.
* `Val c N A = Σ_{n<N} postAtE + (mass − Σ_{n<N} termMassE)` is the bounded
  value of a run: what the effect family `A` collects from the histories
  terminated before depth `N`, plus all mass not yet terminated by then.
* The characterization `PostH_add_NT_le_Val` / `le_PostH_add_NT_of_forall_le_Val`
  says `⨅ N, Val = PostH + NT`, which turns partial correctness into a
  statement provable by induction on the step depth (spec 07 §2).
* The tail sections provide the two frontier shapes the rule soundness
  proofs consume: a deterministic one-step shift, and the depth-1 collapse
  of an atomic program (all successors terminal).
-/

namespace Qhl

open Finset
open scoped NNReal ENNReal ComplexOrder

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## List and `∑'` helpers -/

section Helpers

variable {α M : Type*} [AddCommMonoid M]

theorem sum_map_ite_eq_sum_filter (l : List α) (p : α → Bool) (g : α → M) :
    (l.map fun a => if p a then g a else 0).sum = ((l.filter p).map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases h : p a = true
      · rw [List.filter_cons_of_pos h]
        simp [h, ih]
      · rw [List.filter_cons_of_neg h]
        simp only [List.map_cons, List.sum_cons, if_neg h, zero_add, ih]

theorem ofReal_list_sum {l : List ℝ} (hl : ∀ x ∈ l, 0 ≤ x) :
    ENNReal.ofReal l.sum = (l.map ENNReal.ofReal).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.sum_cons, List.map_cons, List.sum_cons,
        ENNReal.ofReal_add (hl a List.mem_cons_self)
          (List.sum_nonneg fun x hx => hl x (List.mem_cons_of_mem a hx)),
        ih fun x hx => hl x (List.mem_cons_of_mem a hx)]

theorem coe_list_sum_nnreal (l : List ℝ≥0) :
    ((l.sum : ℝ≥0) : ℝ≥0∞) = (l.map fun x => (x : ℝ≥0∞)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Splitting a `ℕ`-indexed `∑'` at `N`. -/
theorem tsum_split (f : ℕ → ℝ≥0∞) (N : ℕ) :
    ∑' n, f n = ∑ n ∈ Finset.range N, f n + ∑' n, f (n + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [ih, Finset.sum_range_succ, add_assoc]
      congr 1
      rw [tsum_eq_zero_add' (f := fun n => f (n + N)) ENNReal.summable]
      simp only [Nat.zero_add]
      congr 1
      exact tsum_congr fun b => by rw [Nat.add_assoc, Nat.add_comm 1 N]

/-- A `∑'` supported at index `1`. -/
theorem tsum_step_one {f : ℕ → ℝ≥0∞} (h0 : f 0 = 0) (hs : ∀ n, f (n + 2) = 0) :
    ∑' n, f n = f 1 := by
  refine tsum_eq_single 1 fun b hb => ?_
  match b with
  | 0 => exact h0
  | 1 => exact absurd rfl hb
  | n + 2 => exact hs n

end Helpers

/-- The frontier at depth `n + 1`, unfolded from the root instead of from the
leaves. -/
theorem boundedFront_succ' (c : Config σT D) (n : ℕ) :
    boundedFront c (n + 1) = (next c).flatMap fun c' => boundedFront c' n := by
  induction n generalizing c with
  | zero =>
      rw [boundedFront_succ, boundedFront_zero]
      simp
  | succ n ih =>
      rw [boundedFront_succ, ih, List.flatMap_assoc]
      simp only [← boundedFront_succ]

/-- A terminated configuration has no successor (predicate form of
`next_done`). -/
theorem next_eq_nil_of_isDone {c : Config σT D} (h : c.isDone = true) :
    next c = [] := by
  obtain ⟨ctrl, σ, ρ⟩ := c
  cases ctrl with
  | done => rfl
  | running P => simp [Config.isDone] at h

/-! ## S-1: terminal-weight sums over frontiers -/

/-- The weight of a configuration: `h` of its state if terminated, else `0`. -/
noncomputable def dVal (h : CQState σT D → ℝ≥0∞) (c : Config σT D) : ℝ≥0∞ :=
  if c.isDone then h c.st else 0

@[simp]
theorem dVal_term (h : CQState σT D → ℝ≥0∞) (t : CQState σT D) :
    dVal h (Config.term t) = h t := rfl

theorem dVal_of_isDone {c : Config σT D} (hc : c.isDone = true)
    (h : CQState σT D → ℝ≥0∞) : dVal h c = h c.st := if_pos hc

theorem dVal_of_not_isDone {c : Config σT D} (hc : c.isDone = false)
    (h : CQState σT D → ℝ≥0∞) : dVal h c = 0 := by
  rw [dVal, hc]
  simp

@[simp]
theorem dVal_init (h : CQState σT D → ℝ≥0∞) (P : Prog σT D) (s : CQState σT D) :
    dVal h (Config.init P s) = 0 :=
  dVal_of_not_isDone (Config.isDone_init P s) h

/-- S-1: the sum of a terminal weight over the frontier at depth `n`. -/
noncomputable def dSum (h : CQState σT D → ℝ≥0∞) (c : Config σT D) (n : ℕ) : ℝ≥0∞ :=
  ((boundedFront c n).map (dVal h)).sum

@[simp]
theorem dSum_zero (h : CQState σT D → ℝ≥0∞) (c : Config σT D) :
    dSum h c 0 = dVal h c := by
  simp [dSum]

/-- The backward unfolding of `dSum`: one step from the root. -/
theorem dSum_succ (h : CQState σT D → ℝ≥0∞) (c : Config σT D) (n : ℕ) :
    dSum h c (n + 1) = ((next c).map fun c' => dSum h c' n).sum := by
  rw [dSum, boundedFront_succ', sum_map_flatMap]
  rfl

theorem dSum_succ_of_isDone {c : Config σT D} (hc : c.isDone = true)
    (h : CQState σT D → ℝ≥0∞) (n : ℕ) : dSum h c (n + 1) = 0 := by
  rw [dSum_succ, next_eq_nil_of_isDone hc]
  rfl

/-- The filtered rendering of `dSum` (the shape of spec 06's `postAt`). -/
theorem dSum_eq_filter (h : CQState σT D → ℝ≥0∞) (c : Config σT D) (n : ℕ) :
    dSum h c n
      = (((boundedFront c n).filter fun c' => c'.isDone).map fun c' => h c'.st).sum := by
  rw [dSum]
  exact sum_map_ite_eq_sum_filter _ _ _

theorem dSum_mono {h h' : CQState σT D → ℝ≥0∞} (hh : ∀ t, h t ≤ h' t)
    (c : Config σT D) (n : ℕ) : dSum h c n ≤ dSum h' c n := by
  refine List.sum_le_sum fun c' _ => ?_
  rw [dVal, dVal]
  split
  · exact hh _
  · exact le_rfl

theorem dSum_congr {h h' : CQState σT D → ℝ≥0∞} (hh : ∀ t, h t = h' t)
    (c : Config σT D) (n : ℕ) : dSum h c n = dSum h' c n := by
  rw [show h = h' from funext hh]

@[simp]
theorem dSum_zero_fun (c : Config σT D) (n : ℕ) :
    dSum (fun _ => (0 : ℝ≥0∞)) c n = 0 := by
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨c', _, rfl⟩ := List.mem_map.mp hx
  rw [dVal]
  split <;> rfl

/-- `dSum` is additive in the weight. -/
theorem dSum_add (f g : CQState σT D → ℝ≥0∞) (c : Config σT D) (n : ℕ) :
    dSum (fun t => f t + g t) c n = dSum f c n + dSum g c n := by
  simp only [dSum]
  generalize boundedFront c n = l
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [dVal, dVal, dVal]
      split <;> [skip; rw [zero_add]] <;> ring

/-- `dSum` commutes with finite sums of weights. -/
theorem dSum_finset_sum {ι : Type*} (s : Finset ι) (f : ι → CQState σT D → ℝ≥0∞)
    (c : Config σT D) (n : ℕ) :
    dSum (fun t => ∑ i ∈ s, f i t) c n = ∑ i ∈ s, dSum (f i) c n := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      simp only [Finset.sum_cons]
      rw [dSum_add, ih]

theorem dVal_tsum {ι : Type*} (f : ι → CQState σT D → ℝ≥0∞) (c : Config σT D) :
    dVal (fun t => ∑' i, f i t) c = ∑' i, dVal (f i) c := by
  by_cases h : c.isDone = true
  · simp only [dVal_of_isDone h]
  · rw [Bool.not_eq_true] at h
    rw [dVal_of_not_isDone h, tsum_congr fun i => dVal_of_not_isDone h (f i), tsum_zero]

/-- `dSum` commutes with countable sums of weights (the frontier is finite and
everything lives in `ℝ≥0∞`). -/
theorem dSum_tsum {ι : Type*} (f : ι → CQState σT D → ℝ≥0∞) (c : Config σT D) (n : ℕ) :
    dSum (fun t => ∑' i, f i t) c n = ∑' i, dSum (f i) c n := by
  simp only [dSum]
  generalize boundedFront c n = l
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih, dVal_tsum]
      exact ENNReal.tsum_add.symm

/-! ## The two instances: expectation and mass -/

/-- The `ℝ≥0∞`-valued expectation of an effect family in a cq-state. -/
noncomputable def expectE (A : σT → EndM D (univ : Finset L)) (s : CQState σT D) :
    ℝ≥0∞ :=
  ENNReal.ofReal (expect A s)

theorem expectE_le_mass {A : σT → EndM D (univ : Finset L)}
    (hA : ∀ σ, IsEffect (A σ)) (s : CQState σT D) :
    expectE A s ≤ (s.q.mass : ℝ≥0∞) := by
  rw [expectE, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (expect_le_mass hA s)

theorem expectE_mono {A B : σT → EndM D (univ : Finset L)}
    (hAB : ∀ σ, A σ ≤ B σ) (s : CQState σT D) : expectE A s ≤ expectE B s := by
  refine ENNReal.ofReal_le_ofReal ?_
  rw [expect, expect]
  exact (Complex.le_def.mp (trace_comp_mono s.q.pos (hAB s.cls))).1

/-- The `ℝ≥0∞` rendering of `postAt`. -/
noncomputable def postAtE (c : Config σT D) (n : ℕ)
    (A : σT → EndM D (univ : Finset L)) : ℝ≥0∞ :=
  dSum (expectE A) c n

/-- The `ℝ≥0∞` rendering of `termMass`. -/
noncomputable def termMassE (c : Config σT D) (n : ℕ) : ℝ≥0∞ :=
  dSum (fun t => (t.q.mass : ℝ≥0∞)) c n

theorem postAtE_eq {A : σT → EndM D (univ : Finset L)}
    (hA : ∀ σ, (A σ).IsPositive) (c : Config σT D) (n : ℕ) :
    postAtE c n A = ENNReal.ofReal (postAt c n A) := by
  rw [postAtE, dSum_eq_filter, postAt, ofReal_list_sum fun x hx => ?_, List.map_map]
  · rfl
  · obtain ⟨c', _, rfl⟩ := List.mem_map.mp hx
    exact expect_nonneg hA c'.st

theorem termMassE_eq (c : Config σT D) (n : ℕ) :
    termMassE c n = (termMass c n : ℝ≥0∞) := by
  rw [termMassE, dSum_eq_filter, termMass]
  generalize ((boundedFront c n).filter fun c' => c'.isDone) = l
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ENNReal.coe_add, ih]
      rfl

/-- `PostH` as a `∑'` of the `ℝ≥0∞` frontier sums. -/
theorem PostH_eq_tsum {A : σT → EndM D (univ : Finset L)}
    (hA : ∀ σ, (A σ).IsPositive) (c : Config σT D) :
    PostH c A = ∑' n, postAtE c n A := by
  rw [PostH]
  exact tsum_congr fun n => (postAtE_eq hA c n).symm

/-- `TermH` as a `∑'` of the `ℝ≥0∞` frontier masses. -/
theorem TermH_eq_tsum (c : Config σT D) : TermH c = ∑' n, termMassE c n := by
  rw [TermH, terminatingTraceMass]
  exact tsum_congr fun n => (termMassE_eq c n).symm

/-- Terminated histories carry at most their mass into the post-expectation
(the `ℝ≥0∞` form of `postAt_le_termMass`). -/
theorem postAtE_le_termMassE {A : σT → EndM D (univ : Finset L)}
    (hA : ∀ σ, IsEffect (A σ)) (c : Config σT D) (n : ℕ) :
    postAtE c n A ≤ termMassE c n :=
  dSum_mono (fun t => expectE_le_mass hA t) c n

theorem postAtE_mono {A B : σT → EndM D (univ : Finset L)}
    (hAB : ∀ σ, A σ ≤ B σ) (c : Config σT D) (n : ℕ) :
    postAtE c n A ≤ postAtE c n B :=
  dSum_mono (fun t => expectE_mono hAB t) c n

theorem PostH_mono {A B : σT → EndM D (univ : Finset L)}
    (hA : ∀ σ, (A σ).IsPositive) (hB : ∀ σ, (B σ).IsPositive)
    (hAB : ∀ σ, A σ ≤ B σ) (c : Config σT D) : PostH c A ≤ PostH c B := by
  rw [PostH_eq_tsum hA, PostH_eq_tsum hB]
  exact ENNReal.tsum_le_tsum fun n => postAtE_mono hAB c n

/-! ## S-1: the bounded value functional -/

/-- The expectation collected by histories terminating before depth `N`. -/
noncomputable def PostUpTo (c : Config σT D) (N : ℕ)
    (A : σT → EndM D (univ : Finset L)) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, postAtE c n A

/-- The mass terminating before depth `N`. -/
noncomputable def TermUpTo (c : Config σT D) (N : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, termMassE c n

theorem TermUpTo_le_mass (c : Config σT D) (N : ℕ) :
    TermUpTo c N ≤ (c.mass : ℝ≥0∞) := by
  have h : TermUpTo c N = ((∑ n ∈ Finset.range N, termMass c n : ℝ≥0) : ℝ≥0∞) := by
    rw [TermUpTo, ENNReal.ofNNReal_finsetSum]
    exact Finset.sum_congr rfl fun n _ => termMassE_eq c n
  rw [h]
  exact ENNReal.coe_le_coe.mpr (sum_termMass_le c N)

theorem TermUpTo_ne_top (c : Config σT D) (N : ℕ) : TermUpTo c N ≠ ∞ :=
  ((TermUpTo_le_mass c N).trans_lt ENNReal.coe_lt_top).ne

theorem TermH_ne_top (c : Config σT D) : TermH c ≠ ∞ :=
  ((terminatingTraceMass_le c).trans_lt ENNReal.coe_lt_top).ne

/-- S-1 (spec 07 §2): the bounded value of a run — what `A` collects before
depth `N`, plus all mass not yet terminated by depth `N`. -/
noncomputable def Val (c : Config σT D) (N : ℕ)
    (A : σT → EndM D (univ : Finset L)) : ℝ≥0∞ :=
  PostUpTo c N A + ((c.mass : ℝ≥0∞) - TermUpTo c N)

@[simp]
theorem Val_zero (c : Config σT D) (A : σT → EndM D (univ : Finset L)) :
    Val c 0 A = (c.mass : ℝ≥0∞) := by
  simp [Val, PostUpTo, TermUpTo]

theorem postAtE_zero_of_not_isDone {c : Config σT D} (hc : c.isDone = false)
    (A : σT → EndM D (univ : Finset L)) : postAtE c 0 A = 0 := by
  rw [postAtE, dSum_zero, dVal_of_not_isDone hc]

theorem termMassE_zero_of_not_isDone {c : Config σT D} (hc : c.isDone = false) :
    termMassE c 0 = 0 := by
  rw [termMassE, dSum_zero, dVal_of_not_isDone hc]

theorem Val_one {c : Config σT D} (hc : c.isDone = false)
    (A : σT → EndM D (univ : Finset L)) : Val c 1 A = (c.mass : ℝ≥0∞) := by
  simp [Val, PostUpTo, TermUpTo, postAtE_zero_of_not_isDone hc,
    termMassE_zero_of_not_isDone hc]

/-- One half of `⨅ N, Val = PostH + NT`: the bounded value over-approximates
the partial-correctness yield of the run at every depth. -/
theorem PostH_add_NT_le_Val {A : σT → EndM D (univ : Finset L)}
    (hA : ∀ σ, IsEffect (A σ)) (c : Config σT D) (N : ℕ) :
    PostH c A + NT c ≤ Val c N A := by
  have hsplit : TermUpTo c N + ∑' n, termMassE c (n + N) = TermH c := by
    rw [TermH_eq_tsum]
    exact (tsum_split _ N).symm
  rw [PostH_eq_tsum (fun σ => (hA σ).isPositive), tsum_split _ N, Val, add_assoc]
  refine add_le_add le_rfl ?_
  calc (∑' n, postAtE c (n + N) A) + NT c
      ≤ (∑' n, termMassE c (n + N)) + NT c :=
        add_le_add (ENNReal.tsum_le_tsum fun n => postAtE_le_termMassE hA c _) le_rfl
    _ ≤ (c.mass : ℝ≥0∞) - TermUpTo c N := by
        refine ENNReal.le_sub_of_add_le_right (TermUpTo_ne_top c N) ?_
        calc (∑' n, termMassE c (n + N)) + NT c + TermUpTo c N
            = (TermUpTo c N + ∑' n, termMassE c (n + N)) + NT c := by ring
          _ = TermH c + NT c := by rw [hsplit]
          _ = (c.mass : ℝ≥0∞) := TermH_add_NTH c
          _ ≤ (c.mass : ℝ≥0∞) := le_rfl

/-- The other half: anything below every bounded value is below
`PostH + NT`. -/
theorem le_PostH_add_NT_of_forall_le_Val {A : σT → EndM D (univ : Finset L)}
    (hA : ∀ σ, (A σ).IsPositive) {c : Config σT D} {x : ℝ≥0∞}
    (hx : ∀ N, x ≤ Val c N A) : x ≤ PostH c A + NT c := by
  have key : ∀ N, x + TermUpTo c N ≤ PostH c A + (c.mass : ℝ≥0∞) := fun N =>
    calc x + TermUpTo c N
        ≤ PostUpTo c N A + ((c.mass : ℝ≥0∞) - TermUpTo c N) + TermUpTo c N :=
          add_le_add (hx N) le_rfl
      _ = PostUpTo c N A + (c.mass : ℝ≥0∞) := by
          rw [add_assoc, tsub_add_cancel_of_le (TermUpTo_le_mass c N)]
      _ ≤ PostH c A + (c.mass : ℝ≥0∞) := by
          refine add_le_add ?_ le_rfl
          rw [PostH_eq_tsum hA]
          exact ENNReal.sum_le_tsum _
  have hsup : x + TermH c ≤ PostH c A + (c.mass : ℝ≥0∞) := by
    have hT : TermH c = ⨆ N, TermUpTo c N := by
      rw [TermH_eq_tsum]
      exact ENNReal.tsum_eq_iSup_nat
    rw [hT, ENNReal.add_iSup]
    exact iSup_le key
  have hTN : TermH c + NT c = (c.mass : ℝ≥0∞) := TermH_add_NTH c
  have hfin : x + TermH c ≤ (PostH c A + NT c) + TermH c := by
    calc x + TermH c ≤ PostH c A + (c.mass : ℝ≥0∞) := hsup
      _ = (PostH c A + NT c) + TermH c := by rw [← hTN]; ring
  exact (ENNReal.add_le_add_iff_right (TermH_ne_top c)).mp hfin

/-! ## Deterministic one-step shift

The frontier shape of `ite` and of the `while` unfolding: a running
configuration with a single successor of the same mass. -/

section Shift

variable {c c' : Config σT D} (hrun : c.isDone = false) (hnext : next c = [c'])
variable {A : σT → EndM D (univ : Finset L)}

include hnext in
theorem dSum_succ_singleton (h : CQState σT D → ℝ≥0∞) (n : ℕ) :
    dSum h c (n + 1) = dSum h c' n := by
  rw [dSum_succ, hnext]
  simp

include hrun hnext in
theorem PostUpTo_succ_singleton (N : ℕ) :
    PostUpTo c (N + 1) A = PostUpTo c' N A := by
  rw [PostUpTo, PostUpTo, Finset.sum_range_succ']
  simp only [postAtE, dSum_succ_singleton hnext, dSum_zero,
    dVal_of_not_isDone hrun, add_zero]

include hrun hnext in
theorem TermUpTo_succ_singleton (N : ℕ) : TermUpTo c (N + 1) = TermUpTo c' N := by
  rw [TermUpTo, TermUpTo, Finset.sum_range_succ']
  simp only [termMassE, dSum_succ_singleton hnext, dSum_zero,
    dVal_of_not_isDone hrun, add_zero]

include hrun hnext in
theorem Val_succ_singleton (hm : c.mass = c'.mass) (N : ℕ) :
    Val c (N + 1) A = Val c' N A := by
  rw [Val, Val, PostUpTo_succ_singleton hrun hnext, TermUpTo_succ_singleton hrun hnext,
    hm]

include hrun hnext in
theorem PostH_singleton (hA : ∀ σ, (A σ).IsPositive) : PostH c A = PostH c' A := by
  rw [PostH_eq_tsum hA, PostH_eq_tsum hA,
    tsum_eq_zero_add' (f := fun n => postAtE c n A) ENNReal.summable]
  simp only [postAtE, dSum_zero, dVal_of_not_isDone hrun, zero_add,
    dSum_succ_singleton hnext]

end Shift

/-! ## Depth-1 collapse of an atomic program

All successors of the root are terminal, so every quantity is carried by the
depth-1 frontier. -/

section Atomic

variable {c : Config σT D} (hrun : c.isDone = false)
  (hdone : ∀ c' ∈ next c, c'.isDone = true)
variable {A : σT → EndM D (univ : Finset L)}

include hdone in
theorem dSum_one_of_all_done (h : CQState σT D → ℝ≥0∞) :
    dSum h c 1 = ((next c).map fun c' => h c'.st).sum := by
  rw [dSum_succ]
  refine congrArg List.sum (List.map_congr_left fun c' hc' => ?_)
  rw [dSum_zero, dVal_of_isDone (hdone c' hc')]

include hdone in
theorem dSum_add_two_of_all_done (h : CQState σT D → ℝ≥0∞) (n : ℕ) :
    dSum h c (n + 2) = 0 := by
  rw [show n + 2 = (n + 1) + 1 from rfl, dSum_succ]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hx
  exact dSum_succ_of_isDone (hdone c' hc') h n

include hrun hdone in
theorem PostH_of_all_done (hA : ∀ σ, (A σ).IsPositive) :
    PostH c A = ((next c).map fun c' => expectE A c'.st).sum := by
  rw [PostH_eq_tsum hA,
    tsum_step_one (f := fun n => postAtE c n A) (postAtE_zero_of_not_isDone hrun A)
      (fun n => dSum_add_two_of_all_done hdone _ n)]
  exact dSum_one_of_all_done hdone _

include hrun hdone in
theorem TermH_of_all_done :
    TermH c = ((next c).map fun c' => (c'.q.mass : ℝ≥0∞)).sum := by
  rw [TermH_eq_tsum,
    tsum_step_one (f := fun n => termMassE c n) (termMassE_zero_of_not_isDone hrun)
      (fun n => dSum_add_two_of_all_done hdone _ n)]
  exact dSum_one_of_all_done hdone _

include hrun hdone in
theorem PostUpTo_of_all_done (N : ℕ) :
    PostUpTo c (N + 2) A = ((next c).map fun c' => expectE A c'.st).sum := by
  induction N with
  | zero =>
      rw [PostUpTo, Finset.sum_range_succ, Finset.sum_range_one,
        postAtE_zero_of_not_isDone hrun, zero_add]
      exact dSum_one_of_all_done hdone _
  | succ N ih =>
      rw [PostUpTo, Finset.sum_range_succ, ← PostUpTo,
        show postAtE c (N + 2) A = 0 from dSum_add_two_of_all_done hdone _ N, add_zero,
        ih]

include hrun hdone in
theorem TermUpTo_of_all_done (N : ℕ) :
    TermUpTo c (N + 2) = ((next c).map fun c' => (c'.q.mass : ℝ≥0∞)).sum := by
  induction N with
  | zero =>
      rw [TermUpTo, Finset.sum_range_succ, Finset.sum_range_one,
        termMassE_zero_of_not_isDone hrun, zero_add]
      exact dSum_one_of_all_done hdone _
  | succ N ih =>
      rw [TermUpTo, Finset.sum_range_succ, ← TermUpTo,
        show termMassE c (N + 2) = 0 from dSum_add_two_of_all_done hdone _ N, add_zero,
        ih]

include hrun hdone in
theorem Val_of_all_done (N : ℕ) :
    Val c (N + 2) A = ((next c).map fun c' => expectE A c'.st).sum
      + ((c.mass : ℝ≥0∞) - ((next c).map fun c' => (c'.q.mass : ℝ≥0∞)).sum) := by
  rw [Val, PostUpTo_of_all_done hrun hdone, TermUpTo_of_all_done hrun hdone]

end Atomic

end Qhl
