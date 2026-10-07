import Qhl.Logic.Source.Rules
import Qhl.Logic.InitComposition
import Qhl.Logic.PreCompute
import Qhl.HSpace.LocalGate

/-! # Source initialization

The printed Axiom-Init resets one selected variable. Its predicate modifier
has the adjoint orientation `∑ n, |n⟩⟨0| A |0⟩⟨n|`. Here the reference basis
state is the `Inhabited` value of that cell, as in the backend initialization.
Selections may depend on the classical store; initialization leaves it unchanged.
-/
namespace Qhl

open Finset

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable [∀ i, Inhabited (D i)] {σT : Type*}

/-- Basis values of a cell index exactly the basis of its singleton register. -/
noncomputable def initSingleIndex (q : L) : D q ≃ QIdx D (Reg.single q).sig where
  toFun := Reg.singleIdx D q
  invFun x := x ⟨q, Reg.self_mem_sig_single q⟩
  left_inv _ := rfl
  right_inv := Reg.idxEquiv_single_const D q (Reg.self_mem_sig_single q)

/-- The cylindrical matrix unit `|m⟩⟨n|` on the selected cell. -/
noncomputable def initMatrixUnit (q : L) (m n : D q) : EndM D (univ : Finset L) :=
  liftF D (subset_univ _) (outerLM (deltav D (Reg.singleIdx D q m))
    (deltav D (Reg.singleIdx D q n)))

private theorem singleIdx_default (q : L) :
    Reg.singleIdx D q default = (default : QIdx D (Reg.single q).sig) := by
  apply (initSingleIndex (D := D) q).symm.injective
  rfl

/-- The printed adjoint sum, with the summation variable a value of the cell,
not a basis index of an arbitrary finite block. -/
theorem SourceAssertion.initSingle_op (A : SourceAssertion σT D) (q : σT → L)
    (σ : σT) :
    (A.initPreSource (fun σ => (Reg.single (q σ)).sig)).quantum.op σ =
      ∑ n : D (q σ), initMatrixUnit (q σ) n default ∘ₗ A.quantum.op σ ∘ₗ
        initMatrixUnit (q σ) default n := by
  change (A.quantum.initPre _).op σ = _
  rw [Assn.initPre_op_eq_sum]
  rw [← (initSingleIndex (D := D) (q σ)).sum_comp]
  apply sum_congr rfl
  intro n _
  simp only [initKraus, initSingleIndex, initMatrixUnit, adjoint_liftF,
    adjoint_outerLM, singleIdx_default]
  rfl

/-- Axiom-Init for partial source derivations. The operator formula is
`SourceAssertion.initSingle_op`; classical condition and domain are retained. -/
theorem SourceDerivPar.axiomInit (A : SourceAssertion σT D) (q : σT → L) :
    SourceDerivPar (A.initPreSource (fun σ => (Reg.single (q σ)).sig))
      (.init (fun σ => (Reg.single (q σ)).sig)) A :=
  .initProg _ A

/-- Axiom-Init for total source derivations. -/
theorem SourceDerivTot.axiomInit (A : SourceAssertion σT D) (q : σT → L) :
    SourceDerivTot (A.initPreSource (fun σ => (Reg.single (q σ)).sig))
      (.init (fun σ => (Reg.single (q σ)).sig)) A :=
  .initProg _ A

/-- Sequential single-variable initialization, with store-dependent selections. -/
def Prog.initSingles : List (σT → L) → Prog σT D
  | [] => .skip
  | q :: qs => .seq (.init (fun σ => (Reg.single (q σ)).sig)) (initSingles qs)

/-- Backward predicate of the singleton sequence, including its empty case. -/
noncomputable def SourceAssertion.initSinglesPre (A : SourceAssertion σT D) :
    List (σT → L) → SourceAssertion σT D
  | [] => A
  | q :: qs => (A.initSinglesPre qs).initPreSource (fun σ => (Reg.single (q σ)).sig)

/-- The macro uses only singleton instances of Axiom-Init, Seq, and Skip. -/
theorem SourceDerivPar.initSingles (A : SourceAssertion σT D) (qs : List (σT → L)) :
    SourceDerivPar (A.initSinglesPre qs) (Prog.initSingles qs) A := by
  induction qs with
  | nil => exact .skip A
  | cons q qs ih => exact .seq (.axiomInit _ q) ih

/-- Total-correctness derivation of the same singleton macro. -/
theorem SourceDerivTot.initSingles (A : SourceAssertion σT D) (qs : List (σT → L)) :
    SourceDerivTot (A.initSinglesPre qs) (Prog.initSingles qs) A := by
  induction qs with
  | nil => exact .skip A
  | cons q qs ih => exact .seq (.axiomInit _ q) ih

/-- No singleton reset changes the store, so every selector retains its value. -/
theorem Prog.initSingles_preservesParameters (qs : List (σT → L))
    {E : Type*} (e : σT → E) :
    (Prog.initSingles (D := D) qs).PreservesParameters e := by
  induction qs with
  | nil => trivial
  | cons q qs ih => exact ⟨trivial, ih⟩

@[simp] theorem SourceAssertion.initSinglesPre_classical (A : SourceAssertion σT D)
    (qs : List (σT → L)) : (A.initSinglesPre qs).classical = A.classical := by
  induction qs with
  | nil => rfl
  | cons q qs ih => exact ih

@[simp] theorem SourceAssertion.initSinglesPre_defined (A : SourceAssertion σT D)
    (qs : List (σT → L)) : (A.initSinglesPre qs).defined = A.defined := by
  induction qs with
  | nil => rfl
  | cons q qs ih => exact ih

/-- The finite block selected by a list of single-variable expressions. -/
def initSingleCells (qs : List (σT → L)) (σ : σT) : Finset L :=
  (qs.map (fun q => q σ)).toFinset

@[simp] theorem SourceAssertion.initPreSource_empty (A : SourceAssertion σT D) :
    A.initPreSource (fun _ => ∅) = A := by
  cases A
  simp only [initPreSource, Assn.initPre_empty]

/-- The block transformer factors into two disjoint reset transformers. -/
theorem SourceAssertion.initPreSource_union (A : SourceAssertion σT D)
    (S T : σT → Finset L) (hd : ∀ σ, Disjoint (S σ) (T σ)) :
    (A.initPreSource T).initPreSource S = A.initPreSource (fun σ => S σ ∪ T σ) := by
  cases A
  simp only [initPreSource, Assn.initPre_union _ S T hd]

/-- Actual backward-transformer equality between a block reset and sequential
single-variable resets. Distinctness is pointwise: addresses may depend on σ. -/
theorem SourceAssertion.initSinglesPre_eq_block (A : SourceAssertion σT D)
    (qs : List (σT → L)) (hd : ∀ σ, (qs.map (fun q => q σ)).Nodup) :
    A.initSinglesPre qs = A.initPreSource (initSingleCells qs) := by
  induction qs with
  | nil =>
    change A = A.initPreSource (fun _ => ∅)
    exact A.initPreSource_empty.symm
  | cons q qs ih =>
    have ht : ∀ σ, (qs.map (fun q => q σ)).Nodup := fun σ =>
      (List.nodup_cons.mp (hd σ)).2
    have hdisj : ∀ σ, Disjoint (Reg.single (q σ)).sig (initSingleCells qs σ) := by
      intro σ
      rw [Reg.sig_single, Finset.disjoint_singleton_left]
      simpa [initSingleCells] using (List.nodup_cons.mp (hd σ)).1
    rw [initSinglesPre, ih ht, initPreSource_union _ _ _ hdisj]
    congr 1
    funext σ
    simp [initSingleCells, Reg.sig_single]

/-- The existing finite-block precondition derives the singleton macro using
only singleton Axiom-Init, Seq, and Skip. -/
theorem SourceDerivPar.initBlockMacro (A : SourceAssertion σT D)
    (qs : List (σT → L)) (hd : ∀ σ, (qs.map (fun q => q σ)).Nodup) :
    SourceDerivPar (A.initPreSource (initSingleCells qs)) (Prog.initSingles qs) A := by
  rw [← A.initSinglesPre_eq_block qs hd]
  exact .initSingles A qs

/-- Total-correctness version of the finite-block macro correspondence. -/
theorem SourceDerivTot.initBlockMacro (A : SourceAssertion σT D)
    (qs : List (σT → L)) (hd : ∀ σ, (qs.map (fun q => q σ)).Nodup) :
    SourceDerivTot (A.initPreSource (initSingleCells qs)) (Prog.initSingles qs) A := by
  rw [← A.initSinglesPre_eq_block qs hd]
  exact .initSingles A qs

/-- Enumerate any fixed finite block by constant selectors. No ordering
assumption is required; `Finset.toList` supplies a duplicate-free enumeration. -/
noncomputable def initBlockSelectors (S : Finset L) : List (σT → L) :=
  S.toList.map (fun q _ => q)

theorem initBlockSelectors_nodup (S : Finset L) (σ : σT) :
    ((initBlockSelectors S).map (fun q => q σ)).Nodup := by
  simpa [initBlockSelectors, List.map_map, Function.comp_def] using S.nodup_toList

@[simp] theorem initSingleCells_blockSelectors (S : Finset L) :
    initSingleCells (initBlockSelectors (σT := σT) S) = fun _ => S := by
  funext σ
  simp [initSingleCells, initBlockSelectors, List.map_map, Function.comp_def]

/-- Every finite block, including the empty block, has a source singleton
macro derivation with exactly the block reset precondition. -/
theorem SourceDerivPar.initFiniteBlock (A : SourceAssertion σT D) (S : Finset L) :
    SourceDerivPar (A.initPreSource (fun _ => S))
      (Prog.initSingles (initBlockSelectors S)) A := by
  simpa only [initSingleCells_blockSelectors] using
    SourceDerivPar.initBlockMacro A (initBlockSelectors S) (initBlockSelectors_nodup S)

theorem SourceDerivTot.initFiniteBlock (A : SourceAssertion σT D) (S : Finset L) :
    SourceDerivTot (A.initPreSource (fun _ => S))
      (Prog.initSingles (initBlockSelectors S)) A := by
  simpa only [initSingleCells_blockSelectors] using
    SourceDerivTot.initBlockMacro A (initBlockSelectors S) (initBlockSelectors_nodup S)

/-- A finite scan resets precisely the cells selected in the unchanged store.
The branches allow the selected block to have a different size in each store. -/
def Prog.initSelected (S : σT → Finset L) : List L → Prog σT D
  | [] => .skip
  | q :: qs => .ite (fun σ => decide (q ∈ S σ))
      (.seq (.init (fun _ => (Reg.single q).sig)) (initSelected S qs))
      (initSelected S qs)

private theorem initPreSource_branch (A : SourceAssertion σT D)
    (U V : σT → Finset L) (φ : σT → Prop)
    (hc : ∀ σ, φ σ → A.classical σ) (he : ∀ σ, φ σ → U σ = V σ) :
    SourceAssertion.Entails ((A.initPreSource U).withClassical φ) (A.initPreSource V) := by
  refine ⟨hc, ?_⟩
  intro σ hσ
  refine ⟨Iff.rfl, fun _ => ?_⟩
  change dualSO D (initLift (U σ)) (A.quantum.op σ) ≤
    dualSO D (initLift (V σ)) (A.quantum.op σ)
  rw [he σ hσ]

/-- Correspondence for an arbitrary store-dependent subset of a duplicate-free
finite scan. The proof uses singleton initialization, conditional, Seq and Skip. -/
theorem initSelected_derivations (A : SourceAssertion σT D) (S : σT → Finset L)
    (qs : List L) (hd : qs.Nodup) :
    SourceDerivPar (A.initPreSource (fun σ => S σ ∩ qs.toFinset))
      (Prog.initSelected S qs) A ∧
    SourceDerivTot (A.initPreSource (fun σ => S σ ∩ qs.toFinset))
      (Prog.initSelected S qs) A := by
  induction qs with
  | nil =>
    simpa [Prog.initSelected] using And.intro (SourceDerivPar.skip A) (SourceDerivTot.skip A)
  | cons q qs ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hd
    obtain ⟨hp, ht⟩ := ih htail
    let T : σT → Finset L := fun σ => S σ ∩ qs.toFinset
    let U : σT → Finset L := fun σ => S σ ∩ (q :: qs).toFinset
    let b : σT → Bool := fun σ => decide (q ∈ S σ)
    have hdisj : ∀ σ, Disjoint (Reg.single q).sig (T σ) := by
      intro σ
      rw [Reg.sig_single, Finset.disjoint_singleton_left]
      simp only [T, Finset.mem_inter, List.mem_toFinset]
      exact fun h => hnot h.2
    have hyes := initPreSource_branch A U (fun σ => (Reg.single q).sig ∪ T σ)
      (fun σ => A.classical σ ∧ b σ = true) (fun _ h => h.1) (by
        intro σ h
        have hm : q ∈ S σ := of_decide_eq_true h.2
        ext j
        simp only [U, T, Reg.sig_single, List.toFinset_cons, Finset.mem_inter,
          Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
        constructor
        · rintro ⟨hj, rfl | ht⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hj, ht⟩
        · rintro (rfl | ⟨hj, ht⟩)
          · exact ⟨hm, Or.inl rfl⟩
          · exact ⟨hj, Or.inr ht⟩)
    have hno := initPreSource_branch A U T
      (fun σ => A.classical σ ∧ b σ = false) (fun _ h => h.1) (by
        intro σ h
        have hm : q ∉ S σ := of_decide_eq_false h.2
        ext j
        simp only [U, T, List.toFinset_cons, Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hj, rfl | ht⟩
          · exact (hm hj).elim
          · exact ⟨hj, ht⟩
        · rintro ⟨hj, ht⟩
          exact ⟨hj, Or.inr ht⟩)
    rw [← SourceAssertion.initPreSource_union A _ T hdisj] at hyes
    constructor
    · apply SourceDerivPar.cond b
      · exact .conseq hyes (.seq (.axiomInit _ (fun _ => q)) hp) (A.entails_refl)
      · exact .conseq hno hp (A.entails_refl)
    · apply SourceDerivTot.cond b
      · exact .conseq hyes (.seq (.axiomInit _ (fun _ => q)) ht) (A.entails_refl)
      · exact .conseq hno ht (A.entails_refl)

/-- Scan the entire finite world to implement any dynamic finite-block reset. -/
noncomputable def Prog.initDynamicBlock (S : σT → Finset L) : Prog σT D :=
  Prog.initSelected S (Finset.univ : Finset L).toList

theorem SourceDerivPar.initDynamicBlock (A : SourceAssertion σT D)
    (S : σT → Finset L) :
    SourceDerivPar (A.initPreSource S) (Prog.initDynamicBlock S) A := by
  simpa [Prog.initDynamicBlock] using
    (initSelected_derivations A S (Finset.univ : Finset L).toList
      (Finset.univ.nodup_toList)).1

theorem SourceDerivTot.initDynamicBlock (A : SourceAssertion σT D)
    (S : σT → Finset L) :
    SourceDerivTot (A.initPreSource S) (Prog.initDynamicBlock S) A := by
  simpa [Prog.initDynamicBlock] using
    (initSelected_derivations A S (Finset.univ : Finset L).toList
      (Finset.univ.nodup_toList)).2

theorem Prog.initSelected_preservesParameters (S : σT → Finset L) (qs : List L)
    {E : Type*} (e : σT → E) : (Prog.initSelected (D := D) S qs).PreservesParameters e := by
  induction qs with
  | nil => trivial
  | cons q qs ih => exact ⟨⟨trivial, ih⟩, ih⟩

/-- The compositional backward transformer of `Prog.initSelected`: each branch
uses the existing conditional transformer and, when selected, singleton reset. -/
noncomputable def Assn.initSelectedPre (A : Assn σT D) (S : σT → Finset L) :
    List L → Assn σT D
  | [] => A
  | q :: qs => Assn.guard (fun σ => decide (q ∈ S σ))
      ((A.initSelectedPre S qs).initPre (fun _ => (Reg.single q).sig))
      (A.initSelectedPre S qs)

/-- Exact operator-transformer equality, independently of source soundness. -/
theorem Assn.initSelectedPre_eq_block (A : Assn σT D) (S : σT → Finset L)
    (qs : List L) (hd : qs.Nodup) :
    A.initSelectedPre S qs = A.initPre (fun σ => S σ ∩ qs.toFinset) := by
  induction qs with
  | nil => simp [initSelectedPre, initPre_empty]
  | cons q qs ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hd
    rw [initSelectedPre, ih htail]
    have hdisj : ∀ σ, Disjoint (Reg.single q).sig (S σ ∩ qs.toFinset) := by
      intro σ
      rw [Reg.sig_single, Finset.disjoint_singleton_left]
      simp only [Finset.mem_inter, List.mem_toFinset]
      exact fun h => hnot h.2
    rw [initPre_union _ _ _ hdisj]
    apply Assn.ext
    funext σ
    by_cases hm : q ∈ S σ
    · rw [Assn.guard_op_of_true (by simpa using hm)]
      have he : S σ ∩ (q :: qs).toFinset = (Reg.single q).sig ∪ (S σ ∩ qs.toFinset) := by
        ext j
        simp only [Reg.sig_single, List.toFinset_cons, Finset.mem_inter,
          Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
        by_cases hj : j = q <;> simp_all
      simp only [Assn.initPre_op, he]
    · rw [Assn.guard_op_of_false (by simpa using hm)]
      have he : S σ ∩ (q :: qs).toFinset = S σ ∩ qs.toFinset := by
        ext j
        simp only [List.toFinset_cons, Finset.mem_inter, Finset.mem_insert]
        by_cases hj : j = q <;> simp_all
      simp only [Assn.initPre_op, he]

/-- Resets and membership tests preserve the classical condition and domain;
the quantum part is the recursive conditional/singleton transformer. -/
noncomputable def SourceAssertion.initSelectedPre (A : SourceAssertion σT D)
    (S : σT → Finset L) (qs : List L) : SourceAssertion σT D where
  classical := A.classical
  defined := A.defined
  quantum := A.quantum.initSelectedPre S qs

/-- Equality of all three source assertion components for the finite scan. -/
theorem SourceAssertion.initSelectedPre_eq_block (A : SourceAssertion σT D)
    (S : σT → Finset L) (qs : List L) (hd : qs.Nodup) :
    A.initSelectedPre S qs = A.initPreSource (fun σ => S σ ∩ qs.toFinset) := by
  cases A
  simp only [initSelectedPre, initPreSource, Assn.initSelectedPre_eq_block _ _ _ hd]

/-- Scanning the whole finite world gives exactly the existing dynamic-block
precondition, including stores selecting an empty block or differing sizes. -/
theorem SourceAssertion.initDynamicBlockPre_eq (A : SourceAssertion σT D)
    (S : σT → Finset L) :
    A.initSelectedPre S (Finset.univ : Finset L).toList = A.initPreSource S := by
  simpa using A.initSelectedPre_eq_block S (Finset.univ : Finset L).toList
    Finset.univ.nodup_toList

end Qhl
