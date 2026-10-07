import Qhl.Logic.Source.StateApproximation
import Qhl.Examples.TrotterTFIMTriple
import Qhl.Logic.StateApproximation
import Qhl.Program.StoreLens

/-!
# TFIM with read-only classical inputs

The quantum world size `n` is fixed. All other numerical inputs, including the
nonnegative requested error tolerance, live in the classical store alongside the two counters.
The program below is made of literal source counted `while` loops.
-/
namespace Qhl.TrotterTFIMClassical
open Qhl Finset TrotterTFIM
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal

structure Params (n : ℕ) where
  N : ℕ
  θ : ℝ
  ca : Fin n → ℝ
  cb : Fin (n - 1) → ℝ
  ε : ℝ≥0

abbrev Store (n : ℕ) := Params n × (ℕ × ℕ)

variable (n : ℕ) [NeZero n]

def outerCounter : CounterLens (Store n) where
  get σ := σ.2.1
  set σ k := (σ.1, k, σ.2.2)
  get_set _ _ := rfl

def innerCounter : CounterLens (Store n) where
  get σ := σ.2.2
  set σ k := (σ.1, σ.2.1, k)
  get_set _ _ := rfl

def xReg : RegExpr (Store n) (QubitL n) 1 := fun σ => TrotterTFIM.xReg n σ.2
def zzReg : RegExpr (Store n) (QubitL n) 2 := fun σ => TrotterTFIM.zzReg n σ.2
noncomputable def xGate (σ : Store n) :=
  TrotterTFIM.xGateE n σ.1.N σ.1.θ σ.1.ca σ.2
noncomputable def zzGate (σ : Store n) :=
  TrotterTFIM.zzGateE n σ.1.N σ.1.θ σ.1.cb σ.2
noncomputable def xLayer : Prog (Store n) (QubitD n) :=
  countedProg (innerCounter n) (fun _ => n) (.unitary 1 (xReg n) (xGate n))
noncomputable def zzLayer : Prog (Store n) (QubitD n) :=
  countedProg (innerCounter n) (fun _ => n - 1) (.unitary 2 (zzReg n) (zzGate n))
noncomputable def slice : Prog (Store n) (QubitD n) := (xLayer n).seq (zzLayer n)
noncomputable def tfimProg : Prog (Store n) (QubitD n) :=
  countedProg (outerCounter n) (fun σ => σ.1.N) (slice n)

variable (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1)

noncomputable def state (k : ℕ) (σ : Store n) :=
  sW n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ k
noncomputable def xState (k : ℕ) (σ : Store n) :=
  chi1 n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1 k
noncomputable def zzState (k : ℕ) (σ : Store n) :=
  chi2 n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1 k

omit [NeZero n] in
include hψ in
theorem norm_state (k : ℕ) (σ : Store n) : ‖state n ψ k σ‖ = 1 :=
  norm_sW n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ hψ k
omit [NeZero n] in
include hψ in
theorem norm_xState (k : ℕ) (σ : Store n) : ‖xState n ψ k σ‖ = 1 :=
  norm_chi1 n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ hψ σ.2.1 k
omit [NeZero n] in
include hψ in
theorem norm_zzState (k : ℕ) (σ : Store n) : ‖zzState n ψ k σ‖ = 1 :=
  norm_chi2 n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ hψ σ.2.1 k

noncomputable def invariant : Assn (Store n) (QubitD n) :=
  Assn.ofStateFam (fun σ => state n ψ σ.2.1 σ) (fun σ => norm_state n ψ hψ _ σ)
noncomputable def middle : Assn (Store n) (QubitD n) :=
  Assn.ofStateFam (zzState n ψ 0) (norm_zzState n ψ hψ 0)
noncomputable def next : Assn (Store n) (QubitD n) :=
  Assn.ofStateFam (fun σ => state n ψ (σ.2.1 + 1) σ) (fun σ => norm_state n ψ hψ _ σ)

/-- A rotation layer preserves an arbitrary predicate of all inputs and the outer counter. -/
theorem xChain (φ : Params n → ℕ → Prop) :
    DerivTot ((invariant n ψ hψ).mask fun σ => φ σ.1 σ.2.1)
      (xLayer n) ((middle n ψ hψ).mask fun σ => φ σ.1 σ.2.1) :=
  DerivTot.countedStateChain_relSource (innerCounter n) n
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (xState n ψ) (norm_xState n ψ hψ) (fun _ _ _ => rfl)
    (fun σ _ => chi1_zero n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1)
    (fun σ _ => chi1_top n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1)
    (DerivTot.countedRung_fam (xReg n) (xGate n)
      (fun σ => norm_xState n ψ hψ σ.2.2 σ)
      (fun σ => norm_xState n ψ hψ (σ.2.2 + 1) σ)
      (fun σ hσ => by
        have hk : σ.2.2 < n := hσ.2
        refine ⟨fun a b _ => Subsingleton.elim a b, ?_⟩
        change Qhl.xGate n σ.1.ca (σ.1.θ / (σ.1.N : ℝ)) (cell n σ.2.2)
            (chi1 n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1 σ.2.2) = _
        rw [show cell n σ.2.2 = ⟨σ.2.2, hk⟩ from cell_eq_mk n hk]
        exact chi1_succ n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1 ⟨σ.2.2, hk⟩))
    (fun _ => DerivTot.unitary_identity_mask _ _
      (fun _ _ _ _ _ => Subsingleton.elim _ _))

theorem zzChain (φ : Params n → ℕ → Prop) :
    DerivTot ((middle n ψ hψ).mask fun σ => φ σ.1 σ.2.1)
      (zzLayer n) ((next n ψ hψ).mask fun σ => φ σ.1 σ.2.1) :=
  DerivTot.countedStateChain_relSource (innerCounter n) (n - 1)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (zzState n ψ) (norm_zzState n ψ hψ) (fun _ _ _ => rfl)
    (fun _ _ => rfl)
    (fun σ _ => chi2_top n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1)
    (DerivTot.countedRung_fam (zzReg n) (zzGate n)
      (fun σ => norm_zzState n ψ hψ σ.2.2 σ)
      (fun σ => norm_zzState n ψ hψ (σ.2.2 + 1) σ)
      (fun σ hσ => by
        have hk : σ.2.2 < n - 1 := hσ.2
        have hne := zzCells_ne n hk
        refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
        change regLift (Reg.pair (cell n σ.2.2) (cell n (σ.2.2 + 1)) hne)
            (TrotterTFIM.zzGateE n σ.1.N σ.1.θ σ.1.cb σ.2)
            (chi2 n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1 σ.2.2) = _
        rw [show TrotterTFIM.zzGateE n σ.1.N σ.1.θ σ.1.cb σ.2 =
            pairGate (D := QubitD n) (cell n σ.2.2) (cell n (σ.2.2 + 1)) hne
              (Rzz (2 * σ.1.cb ⟨σ.2.2, hk⟩ * (σ.1.θ / (σ.1.N : ℝ)))) from by
                simp only [TrotterTFIM.zzGateE, dif_pos hk],
          zzLift_eq n σ.1.cb (σ.1.θ / (σ.1.N : ℝ)) ⟨σ.2.2, hk⟩ hne
            (Fin.ext (cell_val n (by omega))) (Fin.ext (cell_val n (by omega)))]
        exact chi2_succ n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1 ⟨σ.2.2, hk⟩))
    (fun k => DerivTot.unitary_identity_mask _ _ (fun σ hσ =>
      (Reg.pair _ _ (zzCells_ne n (by
        have he : σ.2.2 = k := hσ.2.1
        have hk : k < n - 1 := hσ.2.2
        omega))).inj))

/-- The independent identity-premise of the source total-loop rule. -/
theorem sliceIdentity (φ : Params n → ℕ → Prop) :
    DerivTot ((Assn.one : Assn (Store n) (QubitD n)).mask fun σ => φ σ.1 σ.2.1)
      (slice n) (Assn.one.mask fun σ => φ σ.1 σ.2.1) := by
  apply DerivTot.seq (B := Assn.one.mask fun σ => φ σ.1 σ.2.1)
  · exact DerivTot.countedIdentitySource (innerCounter n) (n := n)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
      (DerivTot.unitary_identity_mask _ _ (fun _ _ _ _ _ => Subsingleton.elim _ _))
      (fun _ => DerivTot.unitary_identity_mask _ _ (fun _ _ _ _ _ => Subsingleton.elim _ _))
  · apply DerivTot.countedIdentitySource (innerCounter n) (n := n - 1)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    · exact DerivTot.unitary_identity_mask _ _ (fun σ hσ =>
        (Reg.pair _ _ (zzCells_ne n hσ.2)).inj)
    · intro k
      exact DerivTot.unitary_identity_mask _ _ (fun σ hσ =>
        (Reg.pair _ _ (zzCells_ne n (by
          have he : σ.2.2 = k := hσ.2.1
          have hk : k < n - 1 := hσ.2.2
          omega))).inj)

noncomputable def exactPre : Assn (Store n) (QubitD n) := Assn.ofState ψ hψ
noncomputable def exactPost : Assn (Store n) (QubitD n) :=
  Assn.ofStateFam (fun σ => state n ψ σ.1.N σ) (fun σ => norm_state n ψ hψ _ σ)

/-- One triple, with parameters evaluated from each input store. All loops use
`whileLoopSource` through the source counted-chain rules. -/
theorem exactDeriv (φ : Params n → Prop) :
    DerivTot ((exactPre n ψ hψ).mask fun σ => φ σ.1) (tfimProg n)
      ((exactPost n ψ hψ).mask fun σ => φ σ.1) :=
  DerivTot.countedStateChainVarSource (outerCounter n) (hv₀ := fun _ => hψ)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (state n ψ) (norm_state n ψ hψ) (fun _ _ _ => rfl)
    (fun σ _ => sW_zero n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ)
    (fun _ _ => rfl)
    ((xChain n ψ hψ (fun p i => φ p ∧ i < p.N)).seq
      (zzChain n ψ hψ (fun p i => φ p ∧ i < p.N)))
    (fun z => sliceIdentity n (fun p i => φ p ∧ i < p.N ∧ (↑(p.N - i) : Int) = z))


/-- Total termination and preservation of every predicate on the read-only
inputs, independently of the quantum input state. -/
theorem identityDeriv (φ : Params n → Prop) :
    DerivTot ((Assn.one : Assn (Store n) (QubitD n)).mask fun σ => φ σ.1)
      (tfimProg n) (Assn.one.mask fun σ => φ σ.1) :=
  DerivTot.countedIdentityVarSource (outerCounter n)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (sliceIdentity n (fun p i => φ p ∧ i < p.N))
    (fun z => sliceIdentity n (fun p i => φ p ∧ i < p.N ∧ (↑(p.N - i) : Int) = z))

/-- The whole program terminates on every quantum input and preserves the
chosen predicate of its read-only classical inputs. -/
theorem identityValid (φ : Params n → Prop) :
    validTot ((Assn.one : Assn (Store n) (QubitD n)).mask fun σ => φ σ.1)
      (tfimProg n) (Assn.one.mask fun σ => φ σ.1) := (identityDeriv n φ).sound

/-- Every classical assignment preserves every numerical input, including ε. -/
theorem preserves_params : (tfimProg n).Preserves (fun σ => σ.1) := by
  simp [tfimProg, slice, xLayer, zzLayer, countedProg, Prog.Preserves,
    outerCounter, innerCounter]

/-- Specializing reads to a fixed input tuple recovers the original program.
The lens is used only for this syntactic equality, not to prove the new triple. -/
def fixedInputs (p : Params n) : StoreLens (ℕ × ℕ) (Store n) where
  get ij := (p, ij)
  put _ σ := σ.2

theorem fixedInputs_program (p : Params n) :
    (tfimProg n).mapStore (fixedInputs n p) =
      TrotterTFIM.tfimProg n p.N p.θ p.ca p.cb := rfl

/-- The actual classical precondition, evaluated from the current store. -/
noncomputable def good (p : Params n) : Prop :=
  p.N ≠ 0 ∧ trotterErrorBound n p.ca p.cb p.N p.θ ≤ (p.ε : ℝ)

/-- The nonnegative requested precision, read from the classical store. -/
def tolerance (σ : Store n) : ℝ := σ.1.ε

omit [NeZero n] in
theorem tolerance_nonneg (σ : Store n) : 0 ≤ tolerance n σ := σ.1.ε.property

noncomputable def target (σ : Store n) := evolution n σ.1.ca σ.1.cb σ.1.θ ψ
omit [NeZero n] in
include hψ in
theorem norm_target (σ : Store n) : ‖target n ψ σ‖ = 1 := by
  exact (norm_evolution n σ.1.ca σ.1.cb σ.1.θ ψ).trans hψ

noncomputable def approxPre : Assn (Store n) (QubitD n) :=
  ((exactPre n ψ hψ).mask fun σ => good n σ.1).scaledBy
    (fun σ => (1 + tolerance n σ)⁻¹)
    (fun σ => approxCoeff_nonneg (tolerance_nonneg n σ))
    (fun σ => approxCoeff_le_one (tolerance_nonneg n σ))

noncomputable def approxPost : Assn (Store n) (QubitD n) :=
  (Assn.ofStateFam (target n ψ) (norm_target n ψ hψ)).approxBy
    (tolerance n) (tolerance_nonneg n)

/-- The requested precision is a store field, the error estimate is a genuine
precondition mask, and no external bound hypothesis is assumed. -/
theorem approxDeriv : DerivTot (approxPre n ψ hψ) (tfimProg n) (approxPost n ψ hψ) := by
  apply (exactDeriv n ψ hψ (good n)).approxBy_stateFam
    (v := target n ψ) (hv := norm_target n ψ hψ)
    (tolerance n) (tolerance_nonneg n)
    ((preserves_params n).comp (fun p => (p.ε : ℝ)))
  intro σ hσ
  letI : NeZero σ.1.N := ⟨hσ.1⟩
  exact norm_wIter_sub_evolution_of_norm_le n σ.1.ca σ.1.cb σ.1.N σ.1.θ ψ hψ σ.1.ε
    ((norm_product_sub_evolution_le n σ.1.ca σ.1.cb σ.1.N σ.1.θ).trans hσ.2)

theorem approxValid : validTot (approxPre n ψ hψ) (tfimProg n) (approxPost n ψ hψ) :=
  (approxDeriv n ψ hψ).sound

omit [NeZero n] in
/-- The precondition reads the requested precision from an admissible store. -/
theorem approxPre_op (σ : Store n) (hσ : good n σ.1) :
    (approxPre n ψ hψ).op σ = (((1 + (σ.1.ε : ℝ))⁻¹ : ℝ) : ℂ) • outerLM ψ ψ := by
  rw [approxPre, Assn.scaledBy_op, Assn.mask_op_of_pos (A := exactPre n ψ hψ)
    (φ := fun τ : Store n => good n τ.1) (σ := σ) hσ]
  rfl

omit [NeZero n] in
theorem approxPost_op (σ : Store n) :
    (approxPost n ψ hψ).op σ = (((1 + (σ.1.ε : ℝ))⁻¹ : ℝ) : ℂ) •
      (outerLM (target n ψ σ) (target n ψ σ) + (σ.1.ε : ℂ) • 1) := by
  simp only [approxPost, Assn.approxBy_op_eq, Assn.ofStateFam_op, tolerance]

omit [NeZero n] in
/-- Fixing the stored inputs recovers the old approximate precondition
at every counter pair satisfying the new classical mask. -/
theorem fixedInputs_pre (p : Params n) (ij : ℕ × ℕ) (hp : good n p) :
    (approxPre n ψ hψ).op (p, ij) =
      (TrotterTFIM.PpreApprox n ψ hψ p.ε p.ε.property).op ij := by
  rw [approxPre_op n ψ hψ (p, ij) hp]
  rfl

omit [NeZero n] in
/-- The store-indexed target effect specializes to the original effect. -/
theorem fixedInputs_post (p : Params n) (ij : ℕ × ℕ) :
    (approxPost n ψ hψ).op (p, ij) =
      (TrotterTFIM.QpostApprox n p.θ p.ca p.cb ψ hψ p.ε p.ε.property).op ij := rfl

noncomputable def inputState (p : Params n) : CQState (Store n) (QubitD n) :=
  ⟨(p, 0, 0), ⟨outerLM ψ ψ, isPositive_outerLM_self ψ⟩⟩

omit [NeZero n] in
/-- The precondition accepts every admissible parameter tuple with positive
weight on its intended pure input. -/
theorem approxPre_expect (p : Params n) (hp : good n p) :
    expectE (approxPre n ψ hψ).op (inputState n ψ p) =
      ENNReal.ofReal ((1 + (p.ε : ℝ))⁻¹) := by
  have hin : (⟪ψ, ψ⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  rw [expectE, expect, approxPre_op n ψ hψ _ hp]
  simp only [inputState, trace_outerLM_comp, LinearMap.smul_apply, outerLM_apply,
    inner_smul_right, hin, mul_one, Complex.ofReal_re]

omit [NeZero n] in
theorem approxPre_expect_pos (p : Params n) (hp : good n p) :
    0 < expectE (approxPre n ψ hψ).op (inputState n ψ p) := by
  rw [approxPre_expect n ψ hψ p hp, ENNReal.ofReal_pos]
  have he : 0 ≤ (p.ε : ℝ) := p.ε.property
  positivity

omit [NeZero n] in
/-- For every nonzero count and every Hamiltonian, the proved error bound
itself supplies an admissible stored tolerance. -/
theorem good_with_bound (p : Params n) (hN : p.N ≠ 0) :
    good n { p with ε := ⟨trotterErrorBound n p.ca p.cb p.N p.θ,
      trotterErrorBound_nonneg n p.ca p.cb p.N p.θ⟩ } := ⟨hN, le_rfl⟩

end Qhl.TrotterTFIMClassical

#print axioms Qhl.TrotterTFIMClassical.identityDeriv
#print axioms Qhl.TrotterTFIMClassical.fixedInputs_program
#print axioms Qhl.TrotterTFIMClassical.fixedInputs_pre
#print axioms Qhl.TrotterTFIMClassical.fixedInputs_post
#print axioms Qhl.TrotterTFIMClassical.exactDeriv
#print axioms Qhl.TrotterTFIMClassical.approxDeriv
#print axioms Qhl.TrotterTFIMClassical.approxValid
#print axioms Qhl.TrotterTFIMClassical.approxPre_expect_pos

/-! # Stored-input TFIM through source derivations -/
namespace Qhl.TrotterTFIMClassical
open Qhl Finset TrotterTFIM
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal
variable (n : ℕ) [NeZero n]
variable (ψ : HS (QubitD n) (univ : Finset (QubitL n))) (hψ : ‖ψ‖ = 1)

/-- The independent identity-premise of the source total-loop rule. -/
theorem sliceIdentitySource (φ : Params n → ℕ → Prop) :
    SourceDerivTot (SourceAssertion.identity (D := QubitD n) (fun σ => φ σ.1 σ.2.1))
      (slice n) (SourceAssertion.identity (D := QubitD n) (fun σ => φ σ.1 σ.2.1)) := by
  apply SourceDerivTot.seq (B := SourceAssertion.identity (D := QubitD n) (fun σ => φ σ.1 σ.2.1))
  · exact SourceDerivTot.countedIdentity (innerCounter n) (fun _ => n) (fun σ => φ σ.1 σ.2.1)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) _
      (SourceDerivTot.unitary_identity _ _ _ (fun _ _ _ _ _ => Subsingleton.elim _ _))
      (fun _ => SourceDerivTot.unitary_identity _ _ _ (fun _ _ _ _ _ => Subsingleton.elim _ _))
  · apply SourceDerivTot.countedIdentity (innerCounter n) (fun _ => n - 1) (fun σ => φ σ.1 σ.2.1)
      (fun _ _ => Iff.rfl) (fun _ _ => rfl) _
    · exact SourceDerivTot.unitary_identity _ _ _ (fun σ hσ =>
        (Reg.pair _ _ (zzCells_ne n hσ.2)).inj)
    · intro k
      exact SourceDerivTot.unitary_identity _ _ _ (fun σ hσ => (Reg.pair _ _ (zzCells_ne n
        hσ.2.1)).inj)

/-- Total termination and preservation of every predicate on the read-only
inputs, independently of the quantum input state. -/
theorem identitySourceDeriv (φ : Params n → Prop) :
    SourceDerivTot (SourceAssertion.identity (D := QubitD n) (fun σ => φ σ.1))
      (tfimProg n) (SourceAssertion.identity (D := QubitD n) (fun σ => φ σ.1)) :=
  SourceDerivTot.countedIdentity (outerCounter n) (fun σ => σ.1.N) (fun σ => φ σ.1)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) _
    (sliceIdentitySource n (fun p i => φ p ∧ i < p.N))
    (fun z => sliceIdentitySource n (fun p i => φ p ∧ i < p.N ∧ (↑(p.N - i) : Int) = z))


/-- Scaled source layers for read-only numerical coefficients. -/
theorem xChainScaledSource (φ : Params n → ℕ → Prop)
    (a : Params n → ℝ) (ha0 : ∀ p, 0 ≤ a p) (ha1 : ∀ p, a p ≤ 1) :
    SourceDerivTot (SourceAssertion.ofAssn ((invariant n ψ hψ).scaledBy (fun σ => a σ.1) (fun σ
        => ha0 σ.1) (fun σ => ha1 σ.1)) (fun σ => φ σ.1 σ.2.1))
      (xLayer n) (SourceAssertion.ofAssn ((middle n ψ hψ).scaledBy (fun σ => a σ.1) (fun σ =>
        ha0 σ.1) (fun σ => ha1 σ.1)) (fun σ => φ σ.1 σ.2.1)) :=
  SourceDerivTot.countedStateChain_scaled (innerCounter n) (fun _ => n) (fun σ => φ σ.1 σ.2.1)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun σ => a σ.1) (fun σ => ha0 σ.1) (fun σ => ha1 σ.1) (fun _ _ => rfl)
    (xState n ψ) (norm_xState n ψ hψ) (fun _ _ _ => rfl)
    (fun σ _ => chi1_zero n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1)
    (fun σ _ => chi1_top n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1)
    (SourceDerivTot.countedRung_fam_scaled (xReg n) (xGate n)
      (fun σ => a σ.1) (fun σ => ha0 σ.1) (fun σ => ha1 σ.1)
      (fun σ => norm_xState n ψ hψ σ.2.2 σ)
      (fun σ => norm_xState n ψ hψ (σ.2.2 + 1) σ)
      (fun σ hσ => by
        have hk : σ.2.2 < n := hσ.2
        refine ⟨fun a b _ => Subsingleton.elim a b, ?_⟩
        change Qhl.xGate n σ.1.ca (σ.1.θ / (σ.1.N : ℝ)) (cell n σ.2.2)
            (chi1 n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1 σ.2.2) = _
        rw [show cell n σ.2.2 = ⟨σ.2.2, hk⟩ from cell_eq_mk n hk]
        exact chi1_succ n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1 ⟨σ.2.2, hk⟩))
    (fun _ => SourceDerivTot.unitary_identity _ _ _
      (fun _ _ _ _ _ => Subsingleton.elim _ _))

theorem zzChainScaledSource (φ : Params n → ℕ → Prop)
    (a : Params n → ℝ) (ha0 : ∀ p, 0 ≤ a p) (ha1 : ∀ p, a p ≤ 1) :
    SourceDerivTot (SourceAssertion.ofAssn ((middle n ψ hψ).scaledBy (fun σ => a σ.1) (fun σ =>
        ha0 σ.1) (fun σ => ha1 σ.1)) (fun σ => φ σ.1 σ.2.1))
      (zzLayer n) (SourceAssertion.ofAssn ((next n ψ hψ).scaledBy (fun σ => a σ.1) (fun σ =>
        ha0 σ.1) (fun σ => ha1 σ.1)) (fun σ => φ σ.1 σ.2.1)) :=
  SourceDerivTot.countedStateChain_scaled (innerCounter n) (fun _ => n - 1) (fun σ => φ σ.1 σ.2.1)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun σ => a σ.1) (fun σ => ha0 σ.1) (fun σ => ha1 σ.1) (fun _ _ => rfl)
    (zzState n ψ) (norm_zzState n ψ hψ) (fun _ _ _ => rfl)
    (fun _ _ => rfl)
    (fun σ _ => chi2_top n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1)
    (SourceDerivTot.countedRung_fam_scaled (zzReg n) (zzGate n)
      (fun σ => a σ.1) (fun σ => ha0 σ.1) (fun σ => ha1 σ.1)
      (fun σ => norm_zzState n ψ hψ σ.2.2 σ)
      (fun σ => norm_zzState n ψ hψ (σ.2.2 + 1) σ)
      (fun σ hσ => by
        have hk : σ.2.2 < n - 1 := hσ.2
        have hne := zzCells_ne n hk
        refine ⟨(Reg.pair _ _ hne).inj, ?_⟩
        change regLift (Reg.pair (cell n σ.2.2) (cell n (σ.2.2 + 1)) hne)
            (TrotterTFIM.zzGateE n σ.1.N σ.1.θ σ.1.cb σ.2)
            (chi2 n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1 σ.2.2) = _
        rw [show TrotterTFIM.zzGateE n σ.1.N σ.1.θ σ.1.cb σ.2 =
            pairGate (D := QubitD n) (cell n σ.2.2) (cell n (σ.2.2 + 1)) hne
              (Rzz (2 * σ.1.cb ⟨σ.2.2, hk⟩ * (σ.1.θ / (σ.1.N : ℝ)))) from by
                simp only [TrotterTFIM.zzGateE, dif_pos hk],
          zzLift_eq n σ.1.cb (σ.1.θ / (σ.1.N : ℝ)) ⟨σ.2.2, hk⟩ hne
            (Fin.ext (cell_val n (by omega))) (Fin.ext (cell_val n (by omega)))]
        exact chi2_succ n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ σ.2.1 ⟨σ.2.2, hk⟩))
    (fun _ => SourceDerivTot.unitary_identity _ _ _ (fun σ hσ =>
      (Reg.pair _ _ (zzCells_ne n hσ.2.1)).inj))

theorem scaledSourceDeriv (φ : Params n → Prop)
    (a : Params n → ℝ) (ha0 : ∀ p, 0 ≤ a p) (ha1 : ∀ p, a p ≤ 1) :
    SourceDerivTot (SourceAssertion.ofAssn ((exactPre n ψ hψ).scaledBy (fun σ => a σ.1) (fun σ
        => ha0 σ.1) (fun σ => ha1 σ.1)) (fun σ => φ σ.1)) (tfimProg n)
      (SourceAssertion.ofAssn ((exactPost n ψ hψ).scaledBy (fun σ => a σ.1) (fun σ => ha0 σ.1)
        (fun σ => ha1 σ.1)) (fun σ => φ σ.1)) :=
  SourceDerivTot.countedStateChain_scaled (outerCounter n) (fun σ => σ.1.N) (fun σ => φ σ.1)
    (hv₀ := fun _ => hψ)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun σ => a σ.1) (fun σ => ha0 σ.1) (fun σ => ha1 σ.1) (fun _ _ => rfl)
    (state n ψ) (norm_state n ψ hψ) (fun _ _ _ => rfl)
    (fun σ _ => sW_zero n σ.1.N σ.1.θ σ.1.ca σ.1.cb ψ)
    (fun _ _ => rfl)
    ((xChainScaledSource n ψ hψ (fun p i => φ p ∧ i < p.N) a ha0 ha1).seq
      (zzChainScaledSource n ψ hψ (fun p i => φ p ∧ i < p.N) a ha0 ha1))
    (fun z => sliceIdentitySource n (fun p i => φ p ∧ i < p.N ∧ (↑(p.N - i) : Int) = z))


/-- Exact evolution preserves the chosen classical input condition. -/
theorem exactSourceDeriv (φ : Params n → Prop) :
    SourceDerivTot (SourceAssertion.ofAssn (exactPre n ψ hψ) (fun σ => φ σ.1)) (tfimProg n)
      (SourceAssertion.ofAssn (exactPost n ψ hψ) (fun σ => φ σ.1)) := by
  have h := scaledSourceDeriv n ψ hψ φ (fun _ => 1) (fun _ => by norm_num)
    (fun _ => by norm_num)
  have hs (A : Assn (Store n) (QubitD n)) :
      A.scaledBy (fun _ => 1) (fun _ => by norm_num) (fun _ => by norm_num) = A := by
    ext σ
    simp [Assn.scaledBy_op]
  simpa only [hs] using h

/-- The exact original masked semantic endpoints, through source soundness. -/
theorem exactSourceValid (φ : Params n → Prop) :
    validTot ((exactPre n ψ hψ).mask (fun σ => φ σ.1)) (tfimProg n)
      ((exactPost n ψ hψ).mask (fun σ => φ σ.1)) := by
  simpa only [SourceAssertion.toAssn_ofAssn] using (exactSourceDeriv n ψ hψ φ).sound

/-- The original identity-predicate triple, through source soundness. -/
theorem identitySourceValid (φ : Params n → Prop) :
    validTot ((Assn.one : Assn (Store n) (QubitD n)).mask fun σ => φ σ.1)
      (tfimProg n) (Assn.one.mask fun σ => φ σ.1) := by
  simpa only [SourceAssertion.identity_toAssn] using (identitySourceDeriv n φ).sound

/-- The paper's stored-input cq precondition keeps admissibility in the classical part. -/
noncomputable def approxSourcePre : SourceAssertion (Store n) (QubitD n) :=
  SourceAssertion.ofAssn
    ((exactPre n ψ hψ).scaledBy (fun σ => (1 + tolerance n σ)⁻¹)
      (fun σ => approxCoeff_nonneg (tolerance_nonneg n σ))
      (fun σ => approxCoeff_le_one (tolerance_nonneg n σ))) (fun σ => good n σ.1)

/-- Approximate source correctness with the actual stored tolerance and classical guard. -/
theorem approxSourceDeriv : SourceDerivTot (approxSourcePre n ψ hψ) (tfimProg n)
    (SourceAssertion.ofAssn (approxPost n ψ hψ) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (scaledSourceDeriv n ψ hψ (good n) (fun p => (1 + (p.ε : ℝ))⁻¹)
      (fun p => approxCoeff_nonneg p.ε.property)
      (fun p => approxCoeff_le_one p.ε.property)) ?_
  apply SourceAssertion.entails_ofAssn
  · intro _ _; trivial
  · intro σ hσ
    rw [Assn.scaledBy_op, approxPost, Assn.approxBy_op_eq]
    apply real_smul_operator_mono _ (approxCoeff_nonneg (tolerance_nonneg n σ))
    apply outerLM_self_le_add_of_norm_sub_le _ _ (norm_state n ψ hψ _ σ)
      (norm_target n ψ hψ σ) (tolerance_nonneg n σ)
    letI : NeZero σ.1.N := ⟨hσ.1⟩
    exact norm_wIter_sub_evolution_of_norm_le n σ.1.ca σ.1.cb σ.1.N σ.1.θ ψ hψ σ.1.ε
      ((norm_product_sub_evolution_le n σ.1.ca σ.1.cb σ.1.N σ.1.θ).trans hσ.2)

/-- Interpretation of the explicit cq precondition is exactly the original predicate. -/
theorem approxSourcePre_toAssn : (approxSourcePre n ψ hψ).toAssn = approxPre n ψ hψ := by
  rw [approxSourcePre, SourceAssertion.toAssn_ofAssn, approxPre, Assn.scaledBy_mask]

/-- The original stored-input approximate semantic triple, through source soundness. -/
theorem approxSourceValid : validTot (approxPre n ψ hψ) (tfimProg n)
    (approxPost n ψ hψ) := by
  have h := (approxSourceDeriv n ψ hψ).sound
  rw [approxSourcePre_toAssn, SourceAssertion.toAssn_ofAssn_true] at h
  exact h

end Qhl.TrotterTFIMClassical

#print axioms Qhl.TrotterTFIMClassical.exactSourceDeriv

#print axioms Qhl.TrotterTFIMClassical.approxSourceDeriv
#print axioms Qhl.TrotterTFIMClassical.approxSourceValid

#print axioms Qhl.TrotterTFIMClassical.identitySourceDeriv
#print axioms Qhl.TrotterTFIMClassical.exactSourceValid
#print axioms Qhl.TrotterTFIMClassical.identitySourceValid
