import Qhl.History.Approx

/-!
# S-2: the bounded sequential decomposition and the composition laws

Subgoal S-2 of spec 07 (design decision V5; the paper arXiv:2412.09869 A.2
uses the same decomposition informally, and (31) is `NT_seqCfg` below).

The whole file rests on **one** induction, `dSum_seqCfg` ((S) of spec 07 §2.2):
for an arbitrary terminal weight `h`, the depth-`n` terminal sum of a run of
`P₁; P₂` splits over the depth `j` at which the `P₁`-phase handed over,

```
dSum h (c.seqCfg P₂) n
  = Σ_{j ≤ n} dSum (fun t => dSum h (Config.init P₂ t) (n − j)) c j.
```

Everything else is an instance (`h := expectE B`, `h := (·.q.mass)`), a
truncation (`PostUpTo_seqCfg`, `TermUpTo_seqCfg`, via `sum_triangle`), or a
limit (`PostH_seqCfg`, `TermH_seqCfg`, `NT_seqCfg`, via `tsum_sum_range_succ`).
Sums live in a commutative monoid, so no ordering bookkeeping is needed.
-/

namespace Qhl

open Finset
open scoped NNReal ENNReal

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## Sum helpers -/

section Helpers

variable {α M : Type*} [AddCommMonoid M]

/-- Swapping a list sum with a `Finset` sum (spec 07 §8 pitfall 7: the bespoke
helper is simpler than translating the list sum into `Finset` language). -/
theorem sum_map_finset_sum {ι : Type*} (l : List α) (u : Finset ι) (f : ι → α → M) :
    (l.map fun a => ∑ j ∈ u, f j a).sum = ∑ j ∈ u, (l.map (f j)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- The triangle reindexing `Σ_{d<n} Σ_{j≤d} = Σ_{j<n} Σ_{i<n−j}`. -/
theorem sum_triangle (f : ℕ → ℕ → M) (n : ℕ) :
    ∑ d ∈ Finset.range n, ∑ j ∈ Finset.range (d + 1), f j (d - j)
      = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range (n - j), f j i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsplit : ∀ j ∈ Finset.range n, ∑ i ∈ Finset.range (n + 1 - j), f j i
          = (∑ i ∈ Finset.range (n - j), f j i) + f j (n - j) := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [show n + 1 - j = (n - j) + 1 by omega, Finset.sum_range_succ]
      rw [Finset.sum_range_succ, ih,
        Finset.sum_range_succ (f := fun j => ∑ i ∈ Finset.range (n + 1 - j), f j i),
        Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
        show n + 1 - n = 1 by omega, Finset.sum_range_one,
        Finset.sum_range_succ (f := fun j => f j (n - j)), Nat.sub_self, add_assoc]

end Helpers

/-! ## S-2: the configuration continued by a second program -/

namespace Config

/-- The configuration `c` with `P₂` appended to whatever it still has to run
(spec 07 §2.2). -/
def seqCfg (c : Config σT D) (P₂ : Prog σT D) : Config σT D :=
  ⟨c.ctrl.seqWith P₂, c.cls, c.q⟩

@[simp]
theorem seqCfg_init (P₁ P₂ : Prog σT D) (s : CQState σT D) :
    Config.init (P₁.seq P₂) s = (Config.init P₁ s).seqCfg P₂ := rfl

@[simp]
theorem mass_seqCfg (c : Config σT D) (P₂ : Prog σT D) :
    (c.seqCfg P₂).mass = c.mass := rfl

/-- `seqCfg` always has something left to run (`seqWith` yields `running` in
both branches). -/
@[simp]
theorem seqCfg_isDone (c : Config σT D) (P₂ : Prog σT D) :
    (c.seqCfg P₂).isDone = false := by
  obtain ⟨ctrl, σ, ρ⟩ := c
  cases ctrl <;> rfl

/-- At a hand-over point the continued configuration *is* the initial
configuration of `P₂`. -/
theorem seqCfg_of_isDone {c : Config σT D} (hc : c.isDone = true) (P₂ : Prog σT D) :
    c.seqCfg P₂ = Config.init P₂ c.st := by
  obtain ⟨ctrl, σ, ρ⟩ := c
  cases ctrl with
  | done => rfl
  | running P => simp [Config.isDone] at hc

end Config

/-- A step of `P₁; P₂` inside the `P₁`-phase is a step of `P₁`, continued. -/
theorem next_seqCfg_of_running {c : Config σT D} (hc : c.isDone = false)
    (P₂ : Prog σT D) :
    next (c.seqCfg P₂) = (next c).map fun c' => c'.seqCfg P₂ := by
  obtain ⟨ctrl, σ, ρ⟩ := c
  cases ctrl with
  | done => simp [Config.isDone] at hc
  | running P => rfl

/-! ## (S): the generic bounded sequential decomposition -/

/-- **(S)** (spec 07 §2.2): the depth-`n` terminal sum of `P₁; P₂` splits over
the depth `j ≤ n` at which the `P₁`-phase terminated. Proved by one induction
on `n`, generalizing the configuration. -/
theorem dSum_seqCfg (h : CQState σT D → ℝ≥0∞) (P₂ : Prog σT D) (c : Config σT D)
    (n : ℕ) :
    dSum h (c.seqCfg P₂) n
      = ∑ j ∈ Finset.range (n + 1),
          dSum (fun t => dSum h (Config.init P₂ t) (n - j)) c j := by
  induction n generalizing c with
  | zero =>
      have hw : (fun t : CQState σT D => dSum h (Config.init P₂ t) (0 - 0))
          = fun _ => (0 : ℝ≥0∞) := by
        funext t
        rw [Nat.sub_self, dSum_zero, dVal_init]
      rw [Finset.sum_range_one, hw, dSum_zero_fun, dSum_zero,
        dVal_of_not_isDone (Config.seqCfg_isDone c P₂)]
  | succ n ih =>
      by_cases hc : c.isDone = true
      · -- the hand-over already happened: only the `j = 0` term survives
        have hz : ∀ i ∈ Finset.range (n + 1),
            dSum (fun t => dSum h (Config.init P₂ t) (n + 1 - (i + 1))) c (i + 1) = 0 :=
          fun i _ => dSum_succ_of_isDone hc _ i
        rw [Config.seqCfg_of_isDone hc, Finset.sum_range_succ',
          Finset.sum_congr rfl hz, Finset.sum_const_zero, zero_add, dSum_zero,
          dVal_of_isDone hc, Nat.sub_zero]
      · -- still inside the `P₁`-phase: unfold one step and use the IH per successor
        rw [Bool.not_eq_true] at hc
        have hz : dSum (fun t => dSum h (Config.init P₂ t) (n + 1 - 0)) c 0 = 0 := by
          rw [dSum_zero, dVal_of_not_isDone hc]
        rw [Finset.sum_range_succ'
            (fun j => dSum (fun t => dSum h (Config.init P₂ t) (n + 1 - j)) c j) (n + 1),
          hz, add_zero, dSum_succ, next_seqCfg_of_running hc, List.map_map,
          show ((next c).map ((fun c'' => dSum h c'' n) ∘ fun c' => c'.seqCfg P₂)).sum
              = ((next c).map fun c' => ∑ j ∈ Finset.range (n + 1),
                  dSum (fun t => dSum h (Config.init P₂ t) (n - j)) c' j).sum from
            congrArg List.sum (List.map_congr_left fun c' _ => ih c'),
          sum_map_finset_sum]
        exact Finset.sum_congr rfl fun j _ => by
          rw [Nat.succ_sub_succ, ← dSum_succ]

/-! ## The two instances -/

/-- (S1): the post-expectation instance of (S). -/
theorem postAtE_seqCfg (B : σT → EndM D (univ : Finset L)) (P₂ : Prog σT D)
    (c : Config σT D) (n : ℕ) :
    postAtE (c.seqCfg P₂) n B
      = ∑ j ∈ Finset.range (n + 1),
          dSum (fun t => postAtE (Config.init P₂ t) (n - j) B) c j :=
  dSum_seqCfg (expectE B) P₂ c n

/-- (S2): the terminal-mass instance of (S). -/
theorem termMassE_seqCfg (P₂ : Prog σT D) (c : Config σT D) (n : ℕ) :
    termMassE (c.seqCfg P₂) n
      = ∑ j ∈ Finset.range (n + 1),
          dSum (fun t => termMassE (Config.init P₂ t) (n - j)) c j :=
  dSum_seqCfg _ P₂ c n

/-! ## Bounded corollaries (the shape consumed by the `while`-par proof) -/

theorem PostUpTo_seqCfg (B : σT → EndM D (univ : Finset L)) (P₂ : Prog σT D)
    (c : Config σT D) (n : ℕ) :
    PostUpTo (c.seqCfg P₂) n B
      = ∑ j ∈ Finset.range n,
          dSum (fun t => PostUpTo (Config.init P₂ t) (n - j) B) c j := by
  rw [PostUpTo, Finset.sum_congr rfl fun d _ => postAtE_seqCfg B P₂ c d,
    sum_triangle (fun j i => dSum (fun t => postAtE (Config.init P₂ t) i B) c j) n]
  exact Finset.sum_congr rfl fun j _ =>
    (dSum_finset_sum _ (fun i t => postAtE (Config.init P₂ t) i B) c j).symm

theorem TermUpTo_seqCfg (P₂ : Prog σT D) (c : Config σT D) (n : ℕ) :
    TermUpTo (c.seqCfg P₂) n
      = ∑ j ∈ Finset.range n,
          dSum (fun t => TermUpTo (Config.init P₂ t) (n - j)) c j := by
  rw [TermUpTo, Finset.sum_congr rfl fun d _ => termMassE_seqCfg P₂ c d,
    sum_triangle (fun j i => dSum (fun t => termMassE (Config.init P₂ t) i) c j) n]
  exact Finset.sum_congr rfl fun j _ =>
    (dSum_finset_sum _ (fun i t => termMassE (Config.init P₂ t) i) c j).symm

/-! ## The diagonal `∑'` reindexing -/

/-- `∑'_d Σ_{j≤d} f j (d−j) = ∑'_j ∑'_i f j i`, via the antidiagonal
partition of `ℕ × ℕ`. -/
theorem tsum_sum_range_succ (F : ℕ → ℕ → ℝ≥0∞) :
    ∑' d, ∑ j ∈ Finset.range (d + 1), F j (d - j) = ∑' j, ∑' i, F j i := by
  have h1 : ∀ d : ℕ, ∑ j ∈ Finset.range (d + 1), F j (d - j)
      = ∑' p : (HasAntidiagonal.antidiagonal d : Finset (ℕ × ℕ)),
          F (p : ℕ × ℕ).1 (p : ℕ × ℕ).2 := by
    intro d
    symm
    rw [Finset.tsum_subtype _ fun q : ℕ × ℕ => F q.1 q.2]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun ij => F ij.1 ij.2) d
  rw [tsum_congr h1,
    ← ENNReal.tsum_sigma'
      (fun p : (Σ d : ℕ, (HasAntidiagonal.antidiagonal d : Finset (ℕ × ℕ))) =>
        F (p.2 : ℕ × ℕ).1 (p.2 : ℕ × ℕ).2),
    ← ENNReal.tsum_prod (f := F)]
  exact HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq fun q : ℕ × ℕ => F q.1 q.2

/-! ## The infinite composition laws (spec 07 §2.3) -/

theorem PostH_seqCfg {B : σT → EndM D (univ : Finset L)}
    (hB : ∀ σ, (B σ).IsPositive) (P₂ : Prog σT D) (c : Config σT D) :
    PostH (c.seqCfg P₂) B
      = ∑' j, dSum (fun t => PostH (Config.init P₂ t) B) c j := by
  rw [PostH_eq_tsum hB, tsum_congr fun d => postAtE_seqCfg B P₂ c d,
    tsum_sum_range_succ fun j i => dSum (fun t => postAtE (Config.init P₂ t) i B) c j]
  refine tsum_congr fun j => ?_
  rw [← dSum_tsum]
  exact dSum_congr (fun t => (PostH_eq_tsum hB _).symm) c j

theorem TermH_seqCfg (P₂ : Prog σT D) (c : Config σT D) :
    TermH (c.seqCfg P₂) = ∑' j, dSum (fun t => TermH (Config.init P₂ t)) c j := by
  rw [TermH_eq_tsum, tsum_congr fun d => termMassE_seqCfg P₂ c d,
    tsum_sum_range_succ fun j i => dSum (fun t => termMassE (Config.init P₂ t) i) c j]
  refine tsum_congr fun j => ?_
  rw [← dSum_tsum]
  exact dSum_congr (fun t => (TermH_eq_tsum _).symm) c j

/-- Paper (31): the nontermination quantity of `P₁; P₂` is that of `P₁` plus
the accumulated nontermination of the `P₂`-phases. Proved additively (V6), by
cancelling `TermH (c.seqCfg P₂)` — which is finite. -/
theorem NT_seqCfg (P₂ : Prog σT D) (c : Config σT D) :
    NT (c.seqCfg P₂) = NT c + ∑' j, dSum (fun t => NT (Config.init P₂ t)) c j := by
  -- each `P₂`-phase splits its initial mass into terminating and nonterminating parts
  have hpt : ∀ t : CQState σT D,
      TermH (Config.init P₂ t) + NT (Config.init P₂ t) = ((t.q.mass : ℝ≥0) : ℝ≥0∞) :=
    fun t => TermH_add_NTH (Config.init P₂ t)
  have hsum : TermH (c.seqCfg P₂) + ∑' j, dSum (fun t => NT (Config.init P₂ t)) c j
      = TermH c := by
    rw [TermH_seqCfg, ← ENNReal.tsum_add, TermH_eq_tsum]
    refine tsum_congr fun j => ?_
    rw [← dSum_add]
    exact dSum_congr hpt c j
  have hfin : TermH (c.seqCfg P₂) + NT (c.seqCfg P₂)
      = TermH (c.seqCfg P₂) + (NT c + ∑' j, dSum (fun t => NT (Config.init P₂ t)) c j) := by
    calc TermH (c.seqCfg P₂) + NT (c.seqCfg P₂)
        = (((c.seqCfg P₂).mass : ℝ≥0) : ℝ≥0∞) := TermH_add_NTH (c.seqCfg P₂)
      _ = ((c.mass : ℝ≥0) : ℝ≥0∞) := by rw [Config.mass_seqCfg]
      _ = TermH c + NT c := (TermH_add_NTH c).symm
      _ = (TermH (c.seqCfg P₂) + ∑' j, dSum (fun t => NT (Config.init P₂ t)) c j)
            + NT c := by rw [hsum]
      _ = TermH (c.seqCfg P₂)
            + (NT c + ∑' j, dSum (fun t => NT (Config.init P₂ t)) c j) := by ring
  exact (ENNReal.add_right_inj (TermH_ne_top (c.seqCfg P₂))).mp hfin

end Qhl
