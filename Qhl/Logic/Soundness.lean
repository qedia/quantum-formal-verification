import Qhl.Logic.Rules

/-!
# L-4 / L-5 / L-6: soundness of `QHL⁺_par` and `QHL⁺_tot`

Subgoals L-4–L-6 of spec 07 (paper arXiv:2412.09869 Thm 6.1, proof A.2).

The model is spec 06's history semantics, untouched. Each rule gets one lemma
following spec 07 §2.6–2.7, and `DerivPar.sound`/`DerivTot.sound` are plain
inductions on the derivation.

The two nontrivial arguments:

* **while (par)** is the paper's finite-stage Claim (37), rendered at the
  granularity of `next`-steps: by `validPar_iff_forall_le_Val` it suffices to
  bound the bounded value `Val` at every depth `N`, and that goes by strong
  induction on `N` through the seq decomposition of the unfolding
  `while b P ⟶ P ; while b P` (V4/V5). No iteration counting, no fuel.
* **while (tot, combined-premise extension)** uses strong
  induction on the ranking value `t σ`: the premise's postcondition is masked
  by `t · < n`, so every hand-over state is strictly smaller and the induction
  hypothesis applies pointwise under `dSum`.
* **while (tot, source rule)** combines the invariant and identity-predicate
  semantic premises using preservation of all input mass. The classical
  invariant supplies nonnegativity before conversion of the integer rank.
  This uses the semantic lemma above, not a converse of soundness.
-/

namespace Qhl

open Finset
open scoped NNReal ENNReal ComplexOrder

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)]
variable {σT : Type*}

/-! ## Small bridges to the step semantics -/

@[simp]
theorem next_init (P : Prog σT D) (s : CQState σT D) :
    next (Config.init P s) = stepProg P s.cls s.q := rfl

omit [∀ i, Inhabited (D i)] in
theorem expect_congr_cls {A B : σT → EndM D (univ : Finset L)} {s : CQState σT D}
    (h : A s.cls = B s.cls) : expect A s = expect B s := by
  rw [expect, expect, h]

omit [∀ i, Inhabited (D i)] in
theorem expectE_congr_cls {A B : σT → EndM D (univ : Finset L)} {s : CQState σT D}
    (h : A s.cls = B s.cls) : expectE A s = expectE B s := by
  rw [expectE, expectE, expect_congr_cls h]

omit [∀ i, Inhabited (D i)] in
@[simp]
theorem expectE_zero_op (s : CQState σT D) :
    expectE (fun _ : σT => (0 : EndM D (univ : Finset L))) s = 0 := by
  rw [expectE, expect]
  simp

/-! ## L-4: the atomic axioms (spec 07 §2.6) — all sound for `⊨tot` -/

/-- The common shape of the atomic soundness proofs: the root is running, all
its successors are terminal, so the whole post-expectation sits on the
depth-one frontier. -/
theorem validTot_of_all_done {P : Prog σT D} {A B : Assn σT D}
    (hdone : ∀ (s : CQState σT D), ∀ c' ∈ next (Config.init P s), c'.isDone = true)
    (hle : ∀ s : CQState σT D, expectE A.op s
      ≤ ((next (Config.init P s)).map fun c' => expectE B.op c'.st).sum) :
    validTot A P B := fun s => by
  rw [PostH_of_all_done (Config.isDone_init P s) (hdone s) fun σ => B.isPositive σ]
  exact hle s

theorem validTot_skip (A : Assn σT D) : validTot A (.skip : Prog σT D) A := by
  refine validTot_of_all_done (fun s c' hc' => ?_) fun s => ?_
  · rw [next_init, stepProg_skip] at hc'
    rw [List.mem_singleton.mp hc']
    rfl
  · rw [next_init, stepProg_skip]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact le_of_eq rfl

theorem validTot_assign (f : σT → σT) (A : Assn σT D) :
    validTot (A.comp f) (.assign f) A := by
  refine validTot_of_all_done (fun s c' hc' => ?_) fun s => ?_
  · rw [next_init, stepProg_assign] at hc'
    rw [List.mem_singleton.mp hc']
    rfl
  · rw [next_init, stepProg_assign]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact le_of_eq rfl

theorem validTot_init (S : σT → Finset L) (A : Assn σT D) :
    validTot (A.initPre S) (.init S) A := by
  refine validTot_of_all_done (fun s c' hc' => ?_) fun s => ?_
  · rw [next_init, stepProg_init] at hc'
    rw [List.mem_singleton.mp hc']
    rfl
  · rw [next_init, stepProg_init]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    refine le_of_eq ?_
    rw [expectE, expectE]
    refine congrArg _ ?_
    rw [expect_congr_cls (A := (A.initPre S).op)
        (B := fun σ => dualSO D (initLift (S s.cls)) (A.op σ)) rfl,
      expect_dualSO A.op (initLift (S s.cls)) (initLift_isQC (S s.cls)).1]
    rfl

theorem validTot_unitary {k : ℕ} (r : RegExpr σT L k)
    (U : ∀ σ, UnitaryOp (TSpace D (r σ))) (A : Assn σT D) :
    validTot (A.unitaryPre r U) (.unitary k r U) A := by
  intro s
  by_cases h : Function.Injective (r s.cls)
  · rw [PostH_of_all_done (Config.isDone_init _ s) (fun c' hc' => ?_)
      fun σ => A.isPositive σ]
    · rw [next_init, stepProg_unitary r U s.cls s.q h]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      refine le_of_eq ?_
      rw [expectE, expectE]
      refine congrArg _ ?_
      rw [expect_congr_cls (A := (A.unitaryPre r U).op)
        (B := fun _ : σT => LinearMap.adjoint (regLift ⟨r s.cls, h⟩ (U s.cls))
          ∘ₗ A.op s.cls ∘ₗ regLift ⟨r s.cls, h⟩ (U s.cls))
        (A.unitaryPre_op_of_dist r U h)]
      exact expect_conj A.op _ s.cls s
    · rw [next_init, stepProg_unitary r U s.cls s.q h] at hc'
      rw [List.mem_singleton.mp hc']
      rfl
  · rw [expectE_congr_cls (B := fun _ : σT => (0 : EndM D (univ : Finset L)))
      (A.unitaryPre_op_of_not_dist r U h), expectE_zero_op]
    exact zero_le

theorem validTot_measure {m k : ℕ} (r : RegExpr σT L k)
    (M : ∀ σ, QMeasure m (TSpace D (r σ))) (upd : Fin m → σT → σT) (A : Assn σT D) :
    validTot (A.measurePre r M upd) (.measure m k r M upd) A := by
  intro s
  by_cases h : Function.Injective (r s.cls)
  · rw [PostH_of_all_done (Config.isDone_init _ s) (fun c' hc' => ?_)
      fun σ => A.isPositive σ]
    · rw [next_init, stepProg_measure r M upd s.cls s.q h, List.map_map]
      refine le_of_eq ?_
      rw [expectE, expect_congr_cls (A := (A.measurePre r M upd).op)
        (B := fun σ => ∑ i, LinearMap.adjoint (regLift ⟨r s.cls, h⟩ ((M s.cls).M i))
          ∘ₗ A.op (upd i σ) ∘ₗ regLift ⟨r s.cls, h⟩ ((M s.cls).M i))
        (A.measurePre_op_of_dist r M upd h),
        expect_sum_conj A.op (fun i => regLift ⟨r s.cls, h⟩ ((M s.cls).M i)) upd s,
        ENNReal.ofReal_sum_of_nonneg fun i _ => expect_nonneg (fun σ => A.isPositive σ) _,
        Fin.sum_univ_def]
      rfl
    · rw [next_init, stepProg_measure r M upd s.cls s.q h] at hc'
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc'
      rfl
  · rw [expectE_congr_cls (B := fun _ : σT => (0 : EndM D (univ : Finset L)))
      (A.measurePre_op_of_not_dist r M upd h), expectE_zero_op]
    exact zero_le

/-! ## L-4: sequential composition (spec 07 §2.7) -/

theorem validTot_seq {A B C : Assn σT D} {P₁ P₂ : Prog σT D}
    (h₁ : validTot A P₁ B) (h₂ : validTot B P₂ C) : validTot A (P₁.seq P₂) C := by
  intro s
  refine (h₁ s).trans ?_
  rw [PostH_eq_tsum (fun σ => B.isPositive σ),
    show Config.init (P₁.seq P₂) s = (Config.init P₁ s).seqCfg P₂ from rfl,
    PostH_seqCfg (fun σ => C.isPositive σ)]
  exact ENNReal.tsum_le_tsum fun j =>
    dSum_mono (fun t => h₂ t) (Config.init P₁ s) j

theorem validPar_seq {A B C : Assn σT D} {P₁ P₂ : Prog σT D}
    (h₁ : validPar A P₁ B) (h₂ : validPar B P₂ C) : validPar A (P₁.seq P₂) C := by
  intro s
  refine (h₁ s).trans ?_
  rw [show Config.init (P₁.seq P₂) s = (Config.init P₁ s).seqCfg P₂ from rfl,
    NT_seqCfg, PostH_seqCfg (fun σ => C.isPositive σ), PostH_eq_tsum (fun σ => B.isPositive σ)]
  calc (∑' j, postAtE (Config.init P₁ s) j B.op) + NT (Config.init P₁ s)
      ≤ (∑' j, dSum (fun t => PostH (Config.init P₂ t) C.op
            + NT (Config.init P₂ t)) (Config.init P₁ s) j) + NT (Config.init P₁ s) :=
        add_le_add (ENNReal.tsum_le_tsum fun j =>
          dSum_mono (fun t => h₂ t) (Config.init P₁ s) j) le_rfl
    _ = ((∑' j, dSum (fun t => PostH (Config.init P₂ t) C.op) (Config.init P₁ s) j)
          + ∑' j, dSum (fun t => NT (Config.init P₂ t)) (Config.init P₁ s) j)
          + NT (Config.init P₁ s) := by
        rw [← ENNReal.tsum_add]
        exact congrArg (· + _) (tsum_congr fun j => dSum_add _ _ _ _)
    _ = (∑' j, dSum (fun t => PostH (Config.init P₂ t) C.op) (Config.init P₁ s) j)
          + (NT (Config.init P₁ s)
            + ∑' j, dSum (fun t => NT (Config.init P₂ t)) (Config.init P₁ s) j) := by
        ring

/-! ## L-4: the conditional (spec 07 §2.7) -/

private theorem next_init_ite (b : σT → Bool) (P₁ P₀ : Prog σT D) (s : CQState σT D) :
    next (Config.init (.ite b P₁ P₀) s)
      = [Config.init (if b s.cls then P₁ else P₀) s] := rfl

theorem validTot_cond {b : σT → Bool} {A₁ A₀ B : Assn σT D} {P₁ P₀ : Prog σT D}
    (h₁ : validTot A₁ P₁ B) (h₀ : validTot A₀ P₀ B) :
    validTot (Assn.guard b A₁ A₀) (.ite b P₁ P₀) B := by
  intro s
  rw [PostH_singleton (Config.isDone_init _ s) (next_init_ite b P₁ P₀ s)
    fun σ => B.isPositive σ]
  by_cases hb : b s.cls = true
  · rw [expectE_guard_of_true hb, if_pos hb]
    exact h₁ s
  · rw [Bool.not_eq_true] at hb
    rw [expectE_guard_of_false hb, if_neg (by simp [hb])]
    exact h₀ s

theorem validPar_cond {b : σT → Bool} {A₁ A₀ B : Assn σT D} {P₁ P₀ : Prog σT D}
    (h₁ : validPar A₁ P₁ B) (h₀ : validPar A₀ P₀ B) :
    validPar (Assn.guard b A₁ A₀) (.ite b P₁ P₀) B := by
  rw [validPar_iff_forall_le_Val] at h₁ h₀ ⊢
  intro s N
  match N with
  | 0 => rw [Val_zero]; exact expectE_le_mass' _ s
  | N + 1 =>
      rw [Val_succ_singleton (Config.isDone_init _ s) (next_init_ite b P₁ P₀ s) rfl]
      by_cases hb : b s.cls = true
      · rw [expectE_guard_of_true hb, if_pos hb]
        exact h₁ s N
      · rw [Bool.not_eq_true] at hb
        rw [expectE_guard_of_false hb, if_neg (by simp [hb])]
        exact h₀ s N

/-! ## L-4: the rule of consequence -/

theorem validTot_conseq {A A' B' B : Assn σT D} {P : Prog σT D}
    (hA : A ≤ A') (h : validTot A' P B') (hB : B' ≤ B) : validTot A P B := fun s =>
  ((expectE_mono hA s).trans (h s)).trans
    (PostH_mono (fun σ => B'.isPositive σ) (fun σ => B.isPositive σ) hB _)

theorem validPar_conseq {A A' B' B : Assn σT D} {P : Prog σT D}
    (hA : A ≤ A') (h : validPar A' P B') (hB : B' ≤ B) : validPar A P B := fun s =>
  ((expectE_mono hA s).trans (h s)).trans
    (add_le_add (PostH_mono (fun σ => B'.isPositive σ) (fun σ => B.isPositive σ) hB _)
      le_rfl)

/-! ## L-4: the loop, partial correctness (paper Claim (37)) -/

private theorem next_init_while_true {b : σT → Bool} (P : Prog σT D) {s : CQState σT D}
    (h : b s.cls = true) :
    next (Config.init (.while b P) s) = [(Config.init P s).seqCfg (.while b P)] := by
  rw [next_init, stepProg_while_true b P s.cls s.q h]
  rfl

private theorem next_init_while_false {b : σT → Bool} (P : Prog σT D) {s : CQState σT D}
    (h : b s.cls = false) :
    next (Config.init (.while b P) s) = [Config.term s] := by
  rw [next_init, stepProg_while_false b P s.cls s.q h]
  rfl

/-- **(R-Loop-par)** is sound. By `validPar_iff_forall_le_Val` the goal is a
statement about the bounded value at every depth `N`; strong induction on `N`,
with the loop body handled through `PostUpTo_seqCfg`/`TermUpTo_seqCfg` at the
unfolding `while b P ⟶ P ; while b P`. -/
theorem validPar_while {b : σT → Bool} {J : Assn σT D} {P : Prog σT D}
    (h : validPar (J.mand b) P J) : validPar J (.while b P) (J.mandNot b) := by
  rw [validPar_iff_forall_le_Val] at h ⊢
  intro s N
  induction N using Nat.strong_induction_on generalizing s with
  | _ N ih =>
    match N with
    | 0 => rw [Val_zero]; exact expectE_le_mass' _ s
    | n + 1 =>
      by_cases hb : b s.cls = true
      · -- the loop unfolds to `P ; while b P`
        rw [Val_succ_singleton (Config.isDone_init _ s) (next_init_while_true P hb) rfl]
        set W : Prog σT D := .while b P with hW
        set c₀ : Config σT D := Config.init P s with hc₀
        set post : σT → EndM D (univ : Finset L) := (J.mandNot b).op with hpost
        -- step 1: the premise, in `Val` form
        have hprem : expectE J.op s
            ≤ PostUpTo c₀ n J.op + ((c₀.mass : ℝ≥0∞) - TermUpTo c₀ n) := by
          rw [← expectE_mand_of_true (A := J) hb]
          exact h s n
        -- step 2: the induction hypothesis at every hand-over point
        have hIH : ∀ j ∈ Finset.range n,
            dSum (expectE J.op) c₀ j
              ≤ dSum (fun t => PostUpTo (Config.init W t) (n - j) post) c₀ j
                + dSum (fun t => ((t.q.mass : ℝ≥0) : ℝ≥0∞)
                    - TermUpTo (Config.init W t) (n - j)) c₀ j := by
          intro j hj
          rw [← dSum_add]
          refine dSum_mono (fun t => ?_) c₀ j
          rw [Finset.mem_range] at hj
          exact ih (n - j) (by omega) t
        have hstep2 : PostUpTo c₀ n J.op
            ≤ PostUpTo (c₀.seqCfg W) n post
              + ∑ j ∈ Finset.range n, dSum (fun t => ((t.q.mass : ℝ≥0) : ℝ≥0∞)
                  - TermUpTo (Config.init W t) (n - j)) c₀ j := by
          rw [PostUpTo_seqCfg, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum hIH
        -- step 3: the slack telescopes into the initial mass
        have hslack : (∑ j ∈ Finset.range n, dSum (fun t => ((t.q.mass : ℝ≥0) : ℝ≥0∞)
              - TermUpTo (Config.init W t) (n - j)) c₀ j)
            + ((c₀.mass : ℝ≥0∞) - TermUpTo c₀ n)
            ≤ ((c₀.seqCfg W).mass : ℝ≥0∞) - TermUpTo (c₀.seqCfg W) n := by
          refine ENNReal.le_sub_of_add_le_right (TermUpTo_ne_top _ _) ?_
          rw [TermUpTo_seqCfg, Config.mass_seqCfg]
          calc (∑ j ∈ Finset.range n, dSum (fun t => ((t.q.mass : ℝ≥0) : ℝ≥0∞)
                  - TermUpTo (Config.init W t) (n - j)) c₀ j)
                + ((c₀.mass : ℝ≥0∞) - TermUpTo c₀ n)
                + ∑ j ∈ Finset.range n,
                    dSum (fun t => TermUpTo (Config.init W t) (n - j)) c₀ j
              = ((∑ j ∈ Finset.range n, dSum (fun t => ((t.q.mass : ℝ≥0) : ℝ≥0∞)
                    - TermUpTo (Config.init W t) (n - j)) c₀ j)
                  + ∑ j ∈ Finset.range n,
                      dSum (fun t => TermUpTo (Config.init W t) (n - j)) c₀ j)
                + ((c₀.mass : ℝ≥0∞) - TermUpTo c₀ n) := by ring
            _ = TermUpTo c₀ n + ((c₀.mass : ℝ≥0∞) - TermUpTo c₀ n) := by
                congr 1
                rw [← Finset.sum_add_distrib, TermUpTo]
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [← dSum_add]
                exact dSum_congr (fun t => tsub_add_cancel_of_le
                  (TermUpTo_le_mass (Config.init W t) (n - j))) c₀ j
            _ = (c₀.mass : ℝ≥0∞) := add_tsub_cancel_of_le (TermUpTo_le_mass c₀ n)
            _ ≤ (c₀.mass : ℝ≥0∞) := le_rfl
        calc expectE J.op s
            ≤ PostUpTo c₀ n J.op + ((c₀.mass : ℝ≥0∞) - TermUpTo c₀ n) := hprem
          _ ≤ (PostUpTo (c₀.seqCfg W) n post
                + ∑ j ∈ Finset.range n, dSum (fun t => ((t.q.mass : ℝ≥0) : ℝ≥0∞)
                    - TermUpTo (Config.init W t) (n - j)) c₀ j)
              + ((c₀.mass : ℝ≥0∞) - TermUpTo c₀ n) := add_le_add hstep2 le_rfl
          _ = PostUpTo (c₀.seqCfg W) n post
              + ((∑ j ∈ Finset.range n, dSum (fun t => ((t.q.mass : ℝ≥0) : ℝ≥0∞)
                    - TermUpTo (Config.init W t) (n - j)) c₀ j)
                + ((c₀.mass : ℝ≥0∞) - TermUpTo c₀ n)) := by ring
          _ ≤ PostUpTo (c₀.seqCfg W) n post
              + (((c₀.seqCfg W).mass : ℝ≥0∞) - TermUpTo (c₀.seqCfg W) n) :=
              add_le_add le_rfl hslack
      · -- the guard is false: the loop terminates in one step
        rw [Bool.not_eq_true] at hb
        match n with
        | 0 => rw [Val_one (Config.isDone_init _ s)]; exact expectE_le_mass' _ s
        | n + 1 =>
            rw [show n + 1 + 1 = n + 2 from rfl,
              Val_of_all_done (Config.isDone_init _ s) (fun c' hc' => ?_)]
            · rw [next_init_while_false P hb]
              simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
              rw [show (Config.term s).st = s from rfl,
                expectE_mandNot_of_false (A := J) hb,
                show ((Config.term s).q.mass : ℝ≥0∞)
                  = ((Config.init (.while b P) s).mass : ℝ≥0∞) from rfl,
                tsub_self, add_zero]
            · rw [next_init_while_false P hb] at hc'
              rw [List.mem_singleton.mp hc']
              rfl

/-! ## L-4: the loop, total correctness -/

/-- The combined-premise total-loop extension is sound.
Strong induction on the ranking value: the
premise's postcondition is masked by `t · < n`, so every hand-over state that
contributes has a strictly smaller ranking and the induction hypothesis
applies pointwise under `dSum`. This replaces the paper's König argument. -/
theorem validTot_while {b : σT → Bool} {J : Assn σT D} {P : Prog σT D} (t : σT → ℕ)
    (h : ∀ n : ℕ, validTot ((J.mand b).mask fun σ => t σ = n) P
      (J.mask fun σ => t σ < n)) :
    validTot J (.while b P) (J.mandNot b) := by
  have key : ∀ n : ℕ, ∀ s : CQState σT D, t s.cls = n →
      expectE J.op s ≤ PostH (Config.init (.while b P) s) (J.mandNot b).op := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs
      by_cases hb : b s.cls = true
      · rw [PostH_singleton (Config.isDone_init _ s) (next_init_while_true P hb)
          fun σ => (J.mandNot b).isPositive σ,
          PostH_seqCfg (fun σ => (J.mandNot b).isPositive σ)]
        have hpre : expectE J.op s
            ≤ PostH (Config.init P s) (J.mask fun σ => t σ < n).op := by
          have hns := h n s
          rwa [expectE_mask_of_pos hs, expectE_mand_of_true hb] at hns
        refine hpre.trans ?_
        rw [PostH_eq_tsum fun σ => (J.mask fun σ => t σ < n).isPositive σ]
        refine ENNReal.tsum_le_tsum fun j => dSum_mono (fun τ => ?_) _ j
        by_cases hτ : t τ.cls < n
        · rw [expectE_mask_of_pos hτ]
          exact ih (t τ.cls) hτ τ rfl
        · rw [expectE_mask_of_neg hτ]
          exact zero_le
      · rw [Bool.not_eq_true] at hb
        rw [PostH_of_all_done (Config.isDone_init _ s) (fun c' hc' => ?_)
          fun σ => (J.mandNot b).isPositive σ]
        · rw [next_init_while_false P hb]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          rw [show (Config.term s).st = s from rfl, expectE_mandNot_of_false (A := J) hb]
        · rw [next_init_while_false P hb] at hc'
          rw [List.mem_singleton.mp hc']
          rfl
  exact fun s => key (t s.cls) s rfl

/-- The premise of `validTot_while` at `n`, with the mask on the precondition
opened. This is the combined-premise extension, not the source rule's
separate identity-predicate decrease premise. -/
theorem validTot_while_premise_apply {b : σT → Bool} {J : Assn σT D} {P : Prog σT D}
    {t : σT → ℕ} {n : ℕ}
    (h : validTot ((J.mand b).mask fun σ => t σ = n) P (J.mask fun σ => t σ < n))
    {s : CQState σT D} (hb : b s.cls = true) (hs : t s.cls = n) :
    expectE J.op s ≤ PostH (Config.init P s) (J.mask fun σ => t σ < n).op := by
  have := h s
  rwa [expectE_mask_of_pos hs, expectE_mand_of_true hb] at this

/-- Classical masks split an output expectation exactly. -/
theorem PostH_mask_split (A : Assn σT D) (φ : σT → Prop) (c : Config σT D) :
    PostH c (A.mask φ).op + PostH c (A.mask fun σ => ¬ φ σ).op = PostH c A.op := by
  rw [PostH_eq_tsum (A.mask φ).isPositive,
    PostH_eq_tsum (A.mask fun σ => ¬ φ σ).isPositive,
    PostH_eq_tsum A.isPositive, ← ENNReal.tsum_add]
  refine tsum_congr fun n => ?_
  rw [postAtE, postAtE, postAtE, ← dSum_add]
  apply dSum_congr
  intro s
  by_cases h : φ s.cls <;> simp [h]

/-- When all input mass terminates in `φ`, masking any effect by `φ` leaves
its output expectation unchanged. -/
theorem PostH_mask_eq_of_mass_le {φ : σT → Prop} (A : Assn σT D)
    (c : Config σT D)
    (h : (c.mass : ℝ≥0∞) ≤ PostH c ((Assn.one : Assn σT D).mask φ).op) :
    PostH c (A.mask φ).op = PostH c A.op := by
  have hgood : PostH c ((Assn.one : Assn σT D).mask φ).op = (c.mass : ℝ≥0∞) :=
    le_antisymm (PostH_le_mass ((Assn.one : Assn σT D).mask φ).isEffect c) h
  have hbad : PostH c ((Assn.one : Assn σT D).mask fun σ => ¬ φ σ).op = 0 := by
    have hh := (PostH_mask_split (Assn.one : Assn σT D) φ c).le.trans
      (PostH_le_mass (Assn.one : Assn σT D).isEffect c)
    rw [hgood] at hh
    have hh' : (c.mass : ℝ≥0∞) + PostH c ((Assn.one : Assn σT D).mask fun σ => ¬ φ σ).op
        ≤ (c.mass : ℝ≥0∞) + 0 := by simpa using hh
    exact le_antisymm ((ENNReal.add_le_add_iff_left (by simp)).mp hh') (zero_le)
  have hAbad : PostH c (A.mask fun σ => ¬ φ σ).op = 0 := by
    apply le_antisymm _ (zero_le)
    rw [← hbad]
    apply PostH_mono (A.mask fun σ => ¬ φ σ).isPositive
      ((Assn.one : Assn σT D).mask fun σ => ¬ φ σ).isPositive
    intro σ
    by_cases hφ : φ σ
    · simp [hφ]
    · simp only [Assn.mask, if_pos hφ, Assn.one_op]
      exact (A.isEffect σ).2
  have hs := PostH_mask_split A φ c
  simpa [hAbad] using hs

/-- Table 3's integer rank and independent identity decrease premises imply
semantic total correctness. The integer lower bound is used only on the
invariant's classical support, after combining the two body premises. -/
theorem validTot_while_source {b : σT → Bool} {A : Assn σT D} {φ : σT → Prop}
    {P : Prog σT D} (t : σT → ℤ)
    (hbound : ∀ σ, φ σ → 0 ≤ t σ)
    (hInv : validTot ((A.mask φ).mand b) P (A.mask φ))
    (hRank : ∀ z : ℤ, validTot
      ((Assn.one : Assn σT D).mask fun σ => φ σ ∧ b σ = true ∧ t σ = z)
      P ((Assn.one : Assn σT D).mask fun σ => t σ < z)) :
    validTot (A.mask φ) (.while b P) ((A.mask φ).mandNot b) := by
  apply validTot_while (fun σ => (t σ).toNat)
  intro n s
  by_cases hφ : φ s.cls
  · by_cases hb : b s.cls = true
    · by_cases hn : (t s.cls).toNat = n
      · rw [expectE_mask_of_pos hn, expectE_mand_of_true hb]
        have hr := hRank (t s.cls) s
        rw [expectE_mask_of_pos ⟨hφ, hb, rfl⟩, expectE_one] at hr
        have heq := PostH_mask_eq_of_mass_le (A.mask φ) (Config.init P s) hr
        have hi := hInv s
        rw [expectE_mand_of_true hb, ← heq] at hi
        refine hi.trans (PostH_mono
          ((A.mask φ).mask fun σ => t σ < t s.cls).isPositive
          ((A.mask φ).mask fun σ => (t σ).toNat < n).isPositive ?_ (Config.init P s))
        intro σ
        by_cases hp : φ σ
        · by_cases ht : t σ < t s.cls
          · have hnat : (t σ).toNat < n := by
              have ha := Int.toNat_of_nonneg (hbound σ hp)
              have hb' := Int.toNat_of_nonneg (hbound s.cls hφ)
              omega
            simp only [Assn.mask, if_pos ht, if_pos hnat]
            exact le_rfl
          · rw [Assn.mask_op_of_neg (φ := fun σ => t σ < t s.cls) ht]
            exact (((A.mask φ).mask fun σ => (t σ).toNat < n).isEffect σ).1
        · by_cases ht : t σ < t s.cls <;>
            simp [Assn.mask, hp, ht]
      · rw [expectE_mask_of_neg hn]
        exact zero_le
    · have hbf : b s.cls = false := by simpa using hb
      by_cases hn : (t s.cls).toNat = n
      · rw [expectE_mask_of_pos hn, expectE_mand_of_false hbf]
        exact zero_le
      · rw [expectE_mask_of_neg hn]
        exact zero_le
  · by_cases hn : (t s.cls).toNat = n
    · rw [expectE_mask_of_pos hn]
      by_cases hb : b s.cls = true
      · rw [expectE_mand_of_true hb, expectE_mask_of_neg hφ]
        exact zero_le
      · rw [expectE_mand_of_false (by simpa using hb)]
        exact zero_le
    · rw [expectE_mask_of_neg hn]
      exact zero_le

/-! ## L-4: the soundness theorems (paper Thm 6.1) -/

/-- **Soundness of `QHL⁺_par`** (paper Thm 6.1, partial half). -/
theorem DerivPar.sound {A B : Assn σT D} {P : Prog σT D} (h : DerivPar A P B) :
    validPar A P B := by
  induction h with
  | skip A => exact (validTot_skip A).validPar
  | assign f A => exact (validTot_assign f A).validPar
  | initProg S A => exact (validTot_init S A).validPar
  | unitary r U A => exact (validTot_unitary r U A).validPar
  | measure r M upd A => exact (validTot_measure r M upd A).validPar
  | seq _ _ ih₁ ih₂ => exact validPar_seq ih₁ ih₂
  | cond _ _ ih₁ ih₀ => exact validPar_cond ih₁ ih₀
  | whileLoop _ ih => exact validPar_while ih
  | conseq hA _ hB ih => exact validPar_conseq hA ih hB

/-- **Soundness of `QHL⁺_tot`** (paper Thm 6.1, total half). -/
theorem DerivTot.sound {A B : Assn σT D} {P : Prog σT D} (h : DerivTot A P B) :
    validTot A P B := by
  induction h with
  | skip A => exact validTot_skip A
  | assign f A => exact validTot_assign f A
  | initProg S A => exact validTot_init S A
  | unitary r U A => exact validTot_unitary r U A
  | measure r M upd A => exact validTot_measure r M upd A
  | seq _ _ ih₁ ih₂ => exact validTot_seq ih₁ ih₂
  | cond _ _ ih₁ ih₀ => exact validTot_cond ih₁ ih₀
  | whileLoop t _ ih => exact validTot_while t ih
  | whileLoopSource t hbound _ _ ihInv ihRank =>
      exact validTot_while_source t hbound ihInv ihRank
  | conseq hA _ hB ih => exact validTot_conseq hA ih hB

/-! ## L-5 / L-6: the bridges to spec 06's judgements -/

/-- L-6: a spec-06 cq-assertion becomes an assertion family by masking with
its classical component (V1). -/
noncomputable def CQAssertion.toAssn (q : CQAssertion σT D) : Assn σT D :=
  (⟨q.op, q.isEffect⟩ : Assn σT D).mask q.cls

@[simp]
theorem CQAssertion.toAssn_op_of_cls {q : CQAssertion σT D} {σ : σT} (h : q.cls σ) :
    q.toAssn.op σ = q.op σ := Assn.mask_op_of_pos h

theorem CQAssertion.toAssn_le {q : CQAssertion σT D} :
    q.toAssn ≤ (⟨q.op, q.isEffect⟩ : Assn σT D) := by
  intro σ
  change ((⟨q.op, q.isEffect⟩ : Assn σT D).mask q.cls).op σ ≤ _
  by_cases h : q.cls σ
  · rw [Assn.mask_op_of_pos h]
  · rw [Assn.mask_op_of_neg h]
    exact (q.isEffect σ).1

/-- L-6: the family judgement implies spec 06's `modelsParH`. One-directional
by design (spec 07's deviation ledger): the family judgement filters terminal
states by the postcondition's classical part, which `modelsParH` does not. -/
theorem modelsParH_of_validPar {q q' : CQAssertion σT D} {P : Prog σT D}
    (h : validPar q.toAssn P q'.toAssn) : modelsParH q P q' := by
  intro s hs
  refine le_trans (le_of_eq ?_) ((h s).trans (add_le_add ?_ le_rfl))
  · exact (expectE_congr_cls (A := q.toAssn.op) (B := q.op)
      (CQAssertion.toAssn_op_of_cls hs)).symm
  · exact PostH_mono (fun σ => (q'.toAssn.isEffect σ).isPositive)
      (fun σ => (q'.isEffect σ).isPositive) CQAssertion.toAssn_le _

/-- L-6: the family judgement implies spec 06's `modelsTotH`. -/
theorem modelsTotH_of_validTot {q q' : CQAssertion σT D} {P : Prog σT D}
    (h : validTot q.toAssn P q'.toAssn) : modelsTotH q P q' := by
  intro s hs
  refine le_trans (le_of_eq ?_) ((h s).trans ?_)
  · exact (expectE_congr_cls (A := q.toAssn.op) (B := q.op)
      (CQAssertion.toAssn_op_of_cls hs)).symm
  · exact PostH_mono (fun σ => (q'.toAssn.isEffect σ).isPositive)
      (fun σ => (q'.isEffect σ).isPositive) CQAssertion.toAssn_le _

/-- L-5/L-6 end-to-end: a `QHL⁺_par` derivation entails spec 06's partial
correctness judgement. -/
theorem modelsParH_of_derivPar {q q' : CQAssertion σT D} {P : Prog σT D}
    (h : DerivPar q.toAssn P q'.toAssn) : modelsParH q P q' :=
  modelsParH_of_validPar h.sound

/-- L-5/L-6 end-to-end: a `QHL⁺_tot` derivation entails spec 06's total
correctness judgement. -/
theorem modelsTotH_of_derivTot {q q' : CQAssertion σT D} {P : Prog σT D}
    (h : DerivTot q.toAssn P q'.toAssn) : modelsTotH q P q' :=
  modelsTotH_of_validTot h.sound

end Qhl
