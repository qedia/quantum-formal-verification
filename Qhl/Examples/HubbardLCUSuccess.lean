import Qhl.Logic.Source.CountedWp
import Qhl.Logic.Source.CountedFamily
import Qhl.Examples.HubbardQSPTriple
import Qhl.Logic.InitBlock
import Qhl.Logic.CountedWp

/-!
# The LCU success-probability triple, internalized

`Qhl/Examples/HubbardLCUTriple.lean` proves the exact evolution triple of the
LCU block encoding and, *outside* the proof system, the Born reading
`effect_reading` at the named output state.  This file **internalizes** the
success-probability conclusion as a `DerivTot`-derived triple over *all*
input states ρ:

* the classical hypothesis `λ(σ) > 0` becomes a **mask** on the
  precondition (consumed by (R-Conseq));
* the success-probability conclusion becomes an **effect precondition**: the
  scaled observable `1_a ⊗ λ⁻² H†H`;
* the ancilla initialisation `q̄_a := ∣0…0⟩` is part of the **program**, so
  (Ax-Init)'s transformer `E†(A) = 1_a ⊗ (⟨0…0∣_a A ∣0…0⟩_a)` turns the
  vacuum-sector compression into a valid global precondition.  (Without the
  `init` statement the compressed precondition would be false in general —
  cross-sector interference.)

**The triple** (`lcuSuccessDeriv` / `lcuSuccessValid`):

```
{ (1_a ⊗ λ⁻² H†H) ∧ λ(σ) > 0 }   q̄_a := ∣0…0⟩ ; prep ; select ; unprep   { ∣0…0⟩⟨0…0∣_a ⊗ 1 }
```

over the widened store `STc = ℕ × ℕ × (t, U)` of the counted circuit, the
coefficients read through `coef`.  Every loop of the circuit is a genuine
counted `while` (`countedProg`), so the backward precondition of each loop is
the **suffix weakest-precondition family** `wpSuffix`
(`Qhl/Logic/CountedWp.lean`): the one-unitary loops (PREPARE, UNPREPARE) are
each ONE `DerivTot.countedWpChain_const` call against the literal-index
transformer family, the compound SELECT loop is ONE
`DerivTot.countedWpBody_const` call whose step is the sign-gate
(Ax-Uni)/(R-Conseq) rung glued by (R-Seq) to the `φ`-relativised
`DerivTot.countedWpChain` of the inner letter loop.  So the derivation uses
(Ax-Init) + (Ax-Uni) + (Ax-Ass) + (R-Seq) + (R-Conseq) + (R-Loop-tot) only
(the counted-`while` layer is itself packaged from these printed rules).

**Reading**: for every input ρ, the probability that the ancilla block reads
all-zero after the circuit is at least `λ⁻² · Tr(ρ (1_a ⊗ H†H))` — at the
intended pure input `∣0⟩_a ⊗ ψ` this floor is `λ⁻²‖Hψ‖²`, which
`effect_reading` shows is *exactly* the success probability: the triple is
tight (`succPre_expect_pure`).

The (R-Conseq) entailment is where the operator theorems of the LCU lane now
serve as conseq lemmas: each `wpSuffix` family is displayed as one
conjugation by its semantic chain operator (`wpSuffix_zero_op_conj` plus the
`chainOp` bridges below), so the folded precondition of the whole circuit is
`W† P₀ W` (`wpLCU_op`); (Ax-Init) compresses it to the vacuum block
(`initPre_ancCells_op`), and the block-encoding identity `blockEncoding`
identifies that block with `λ⁻² H†H` (`succBlock_eq_conj`).

Non-vacuity: `succPre_witness` gives an explicit store (counters `0`,
`(t, U) = (0, 1)`) and an explicit computational-basis input with strictly
positive precondition expectation, using that the interaction Hamiltonian is
diagonal (`hubbard_diag`) with a doubly-occupied adjacent pair.
-/

namespace Qhl.HubbardLCUSuccess

open Qhl Qhl.HubbardLCU Qhl.HubbardQSP Qhl.BravyiKitaev Finset
open scoped ComplexInnerProductSpace ComplexOrder NNReal ENNReal

section

variable (x : ℕ) (hx : 0 < x)

/-! ## §1. The program: ancilla initialisation, then the LCU circuit -/

/-- The ancilla block of the LCU world, as a cell set. -/
def ancS : Finset (WL x) := ancCells (SysL x) (AncL x)

/-- **The LCU success program**: the literal ancilla initialisation
`q̄_a := ∣0…0⟩`, then the block-encoding circuit `prep ; select ; unprep`
(each loop a genuine counted `while` over the widened store `STc`). -/
noncomputable def lcuInitProg : Prog STc (QubitCells (WL x)) :=
  (Prog.init fun _ => ancS x).seq (lcuProg x hx)

/-! ## §2. The endpoint assertions -/

/-- The postcondition: the ancilla-vacuum effect `∣0…0⟩⟨0…0∣_a ⊗ 1`. -/
noncomputable def vacPost : Assn STc (QubitCells (WL x)) :=
  ⟨fun _ => ancZeroEff x, fun _ => isEffect_ancZeroEff x⟩

@[simp]
theorem vacPost_op (σ : STc) : (vacPost x).op σ = ancZeroEff x := rfl

theorem lam_nonneg (σ : ST) : 0 ≤ lam x σ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The system-block success observable `λ⁻² H†H` (the zero operator where
`λ = 0`, since `(0 : ℝ)⁻¹ = 0`). -/
noncomputable def succBlock (σ : ST) : EndM (QubitCells (SysL x)) (univ : Finset (SysL x)) :=
  (((lam x σ)⁻¹ ^ 2 : ℝ) : ℂ) •
    (LinearMap.adjoint (hubbardOp x σ.1 σ.2) ∘ₗ hubbardOp x σ.1 σ.2)

/-- The block-encoding identity, as a linear-map equality: the vacuum-block
compression of the circuit operator is `λ⁻¹ H`. -/
theorem blockOp_eq (σ : ST) (hlam : 0 < lam x σ) :
    LinearMap.adjoint (sysEmb x) ∘ₗ lcuOp x hx σ ∘ₗ sysEmb x
      = (((lam x σ)⁻¹ : ℝ) : ℂ) • hubbardOp x σ.1 σ.2 := by
  refine LinearMap.ext fun ψ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, lcuOp_emb x hx σ ψ,
    LinearMap.smul_apply]
  exact blockEncoding x hx ψ σ hlam

/-- `λ⁻² H†H` is the conjugation of the identity by the block compression
`E† ∘ W ∘ E` of the circuit — the shape the wp computation lands on. -/
theorem succBlock_eq_conj (σ : ST) (hlam : 0 < lam x σ) :
    LinearMap.adjoint (LinearMap.adjoint (sysEmb x) ∘ₗ lcuOp x hx σ ∘ₗ sysEmb x) ∘ₗ
        (LinearMap.adjoint (sysEmb x) ∘ₗ lcuOp x hx σ ∘ₗ sysEmb x)
      = succBlock x σ := by
  rw [blockOp_eq x hx σ hlam, ← LinearMap.star_eq_adjoint, star_smul,
    LinearMap.star_eq_adjoint, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
    show star ((((lam x σ)⁻¹ : ℝ) : ℂ)) * (((lam x σ)⁻¹ : ℝ) : ℂ)
        = (((lam x σ)⁻¹ ^ 2 : ℝ) : ℂ) from by
      rw [RCLike.star_def, Complex.conj_ofReal]
      push_cast
      ring]
  rfl

/-- `E†` of the world is a contraction (the range projector `∣0⟩⟨0∣_a ⊗ 1` is
an effect). -/
theorem norm_embAdj_le (y : HS (QubitCells (WL x)) (univ : Finset (WL x))) :
    ‖LinearMap.adjoint (sysEmb x) y‖ ≤ ‖y‖ := by
  have hinner : (⟪y, ancZeroEff x y⟫ : ℂ)
      = ((‖LinearMap.adjoint (sysEmb x) y‖ : ℝ) : ℂ) ^ 2 := by
    rw [show ancZeroEff x y = sysEmb x (LinearMap.adjoint (sysEmb x) y) from rfl,
      ← LinearMap.adjoint_inner_left,
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (LinearMap.adjoint (sysEmb x) y),
      RCLike.ofReal_eq_complex_ofReal]
  have hy : (⟪y, y⟫ : ℂ) = ((‖y‖ : ℝ) : ℂ) ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) y, RCLike.ofReal_eq_complex_ofReal]
  have hle := (le_iff_inner_le _ _).mp (isEffect_ancZeroEff x).2 y
  rw [Module.End.one_apply, hinner, hy] at hle
  have h2 : ‖LinearMap.adjoint (sysEmb x) y‖ ^ 2 ≤ ‖y‖ ^ 2 := by exact_mod_cast hle
  nlinarith [norm_nonneg (LinearMap.adjoint (sysEmb x) y), norm_nonneg y]

include hx in
/-- The success observable is an effect for **every** store value. -/
theorem isEffect_succBlock (σ : ST) : IsEffect (succBlock x σ) := by
  rcases lt_or_ge 0 (lam x σ) with hlam | hlam
  · rw [← succBlock_eq_conj x hx σ hlam]
    set K := LinearMap.adjoint (sysEmb x) ∘ₗ lcuOp x hx σ ∘ₗ sysEmb x with hK
    have hKnorm : ∀ u, ‖K u‖ ≤ ‖u‖ := by
      intro u
      calc ‖K u‖
          = ‖LinearMap.adjoint (sysEmb x) (lcuOp x hx σ (sysEmb x u))‖ := rfl
        _ ≤ ‖lcuOp x hx σ (sysEmb x u)‖ := norm_embAdj_le x _
        _ = ‖sysEmb x u‖ := norm_apply_of_isUnitary (isUnitary_lcuOp x hx σ) _
        _ = ‖u‖ := norm_ancEmbed _ _
    constructor
    · rw [LinearMap.nonneg_iff_isPositive, isPositive_iff_inner_nonneg]
      intro u
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
        inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (K u), RCLike.ofReal_eq_complex_ofReal,
        ← Complex.ofReal_pow]
      exact Complex.zero_le_real.mpr (sq_nonneg _)
    · rw [le_iff_inner_le]
      intro u
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, Module.End.one_apply,
        inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (K u),
        inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u, RCLike.ofReal_eq_complex_ofReal,
        ← Complex.ofReal_pow, ← Complex.ofReal_pow, Complex.real_le_real]
      nlinarith [hKnorm u, norm_nonneg (K u), norm_nonneg u]
  · have h0 : lam x σ = 0 := le_antisymm hlam (lam_nonneg x σ)
    rw [show succBlock x σ = 0 from by
      rw [succBlock, h0]
      norm_num]
    exact isEffect_zero

/-- **The internalized success precondition**: the effect `1_a ⊗ λ⁻² H†H`,
masked by the classical hypothesis `λ(σ) > 0` — at the widened store, the
coefficients read through `coef`. -/
noncomputable def succPre : Assn STc (QubitCells (WL x)) :=
  Assn.mask
    ⟨fun σ => sysLift (L₂ := AncL x) (succBlock x (coef σ)),
      fun σ => isEffect_sysLift (isEffect_succBlock x hx (coef σ))⟩
    fun σ => 0 < lam x (coef σ)

/-! ## §3. The literal-index transformer families and their chain operators

Each counted loop's body is a store-read (Ax-Uni); the counted-`wp` rules
consume a **literal-index** transformer family `g k` that agrees with the
store-read transformer on the step mask (where the stored counter *is* `k`).
Each family is displayed as a conjugation by a per-pass operator, and the
`chainOp` of the ordered pass list is identified with the semantic chain
operator of the lane (`prepChain`/`ctrlChain`/`selOp`/`unprepChain`). -/

/-- The literal-`k` backward transformer of one PREPARE pass: (Ax-Uni) at the
Givens pair of position `k`, the angle read from the coefficients. -/
noncomputable def prepT (k : ℕ) (A : Assn STc (QubitCells (WL x))) :
    Assn STc (QubitCells (WL x)) :=
  A.unitaryPre (RegExpr.const (prepReg x (jCell x hx k)))
    (fun σ => pairGate (D := QubitCells (WL x)) (aC x (jA x (jCell x hx k)))
      (aC x (jB x (jCell x hx k))) (jA_ne_jB x (jCell x hx k))
      (givens (ang x hx (coef σ) ((jCell x hx k : Fin (HubbardLCU.NT x - 1)) : ℕ)
        (jA_lt x (jCell x hx k)))))

/-- The PREPARE gate at a `Fin` position (the `prepChain` lambda, named). -/
noncomputable def prepGF (τ : ST) (j : Fin (HubbardLCU.NT x - 1)) :
    EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  regLift (prepReg x j)
    ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
      (jA_ne_jB x j) (givens (ang x hx τ (j : ℕ) (jA_lt x j)))) :
      TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _)

/-- The PREPARE pass operator at the literal counter value. -/
noncomputable def prepG (τ : ST) (k : ℕ) :
    EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  prepGF x hx τ (jCell x hx k)

theorem prepT_op (k : ℕ) (A : Assn STc (QubitCells (WL x))) (σ : STc) :
    (prepT x hx k A).op σ
      = LinearMap.adjoint (prepG x hx (coef σ) k) ∘ₗ A.op σ ∘ₗ prepG x hx (coef σ) k :=
  Assn.unitaryPre_const_op A (prepReg x (jCell x hx k))
    (fun σ' => pairGate (D := QubitCells (WL x)) (aC x (jA x (jCell x hx k)))
      (aC x (jB x (jCell x hx k))) (jA_ne_jB x (jCell x hx k))
      (givens (ang x hx (coef σ') ((jCell x hx k : Fin (HubbardLCU.NT x - 1)) : ℕ)
        (jA_lt x (jCell x hx k))))) σ

/-- The ordered PREPARE pass list is the PREPARE Givens chain. -/
theorem chainOp_prepG (τ : ST) :
    chainOp (List.range (HubbardLCU.NT x - 1)) (prepG x hx τ) = prepChain x hx τ := by
  have h := chainOp_range_of_get (List.finRange (HubbardLCU.NT x - 1))
    (prepG x hx τ) (fun j => prepGF x hx τ j) (fun j hj => by
      have hjn : j < HubbardLCU.NT x - 1 := by rwa [List.length_finRange] at hj
      have hget : (List.finRange (HubbardLCU.NT x - 1)).get ⟨j, hj⟩
          = (⟨j, hjn⟩ : Fin (HubbardLCU.NT x - 1)) := by
        simp [List.get_eq_getElem, List.getElem_finRange]
      rw [hget]
      change prepGF x hx τ (jCell x hx j) = prepGF x hx τ ⟨j, hjn⟩
      rw [jCell_eq_mk x hx hjn])
  rw [List.length_finRange] at h
  exact h.trans rfl

/-- The literal-`(k, m)` backward transformer of one letter pass of SELECT
rung `k`: (Ax-Uni) at the controlled letter of term `k`, site `m`. -/
noncomputable def letterT (k m : ℕ) (A : Assn STc (QubitCells (WL x))) :
    Assn STc (QubitCells (WL x)) :=
  A.unitaryPre (RegExpr.const (ctrlReg x (lCell x hx k) (sCell x m)))
    (fun _ => pairGate (D := QubitCells (WL x)) (aC x (lCell x hx k))
      (sC x (sCell x m)) Sum.inr_ne_inl
      (control (str x (lCell x hx k) (sCell x m)).gate))

/-- The controlled letter of rung `k` at a `Fin` site (the `ctrlChain`
lambda, named). -/
noncomputable def letterGF (k : ℕ) (s : SysL x) :
    EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  regLift (ctrlReg x (lCell x hx k) s)
    ((pairGate (D := QubitCells (WL x)) (aC x (lCell x hx k)) (sC x s) Sum.inr_ne_inl
      (control (str x (lCell x hx k) s).gate)) :
      TSpace (QubitCells (WL x)) (ctrlReg x (lCell x hx k) s).toFun →ₗ[ℂ] _)

/-- The letter pass operator at the literal counter values. -/
noncomputable def letterG (k m : ℕ) :
    EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  letterGF x hx k (sCell x m)

theorem letterT_op (k m : ℕ) (A : Assn STc (QubitCells (WL x))) (σ : STc) :
    (letterT x hx k m A).op σ
      = LinearMap.adjoint (letterG x hx k m) ∘ₗ A.op σ ∘ₗ letterG x hx k m :=
  Assn.unitaryPre_const_op A (ctrlReg x (lCell x hx k) (sCell x m))
    (fun _ => pairGate (D := QubitCells (WL x)) (aC x (lCell x hx k))
      (sC x (sCell x m)) Sum.inr_ne_inl
      (control (str x (lCell x hx k) (sCell x m)).gate)) σ

/-- The ordered letter pass list of rung `k` is its controlled-letter chain. -/
theorem chainOp_letterG (k : ℕ) :
    chainOp (List.range (2 ^ x)) (letterG x hx k) = ctrlChain x (lCell x hx k) := by
  have h := chainOp_range_of_get (List.finRange (2 ^ x))
    (letterG x hx k) (fun s => letterGF x hx k s) (fun m hm => by
      have hmn : m < 2 ^ x := by rwa [List.length_finRange] at hm
      have hget : (List.finRange (2 ^ x)).get ⟨m, hm⟩ = (⟨m, hmn⟩ : SysL x) := by
        simp [List.get_eq_getElem, List.getElem_finRange]
      rw [hget]
      change letterGF x hx k (sCell x m) = letterGF x hx k ⟨m, hmn⟩
      rw [sCell_eq_mk x hmn])
  rw [List.length_finRange] at h
  exact h.trans rfl

/-- The literal-`k` backward transformer of one whole SELECT rung: the suffix
`wp` family of the letter loop, then the sign-gate (Ax-Uni). -/
noncomputable def rungT (k : ℕ) (A : Assn STc (QubitCells (WL x))) :
    Assn STc (QubitCells (WL x)) :=
  (wpSuffix (letterT x hx k) (2 ^ x) A 0).unitaryPre
    (RegExpr.const (Reg.single (aC x (lCell x hx k))))
    (fun σ => singleGate (QubitCells (WL x)) (aC x (lCell x hx k))
      (sgnGate (cf x (coef σ) (lCell x hx k))))

/-- The rung chain operator (over `Fin` positions) is the SELECT operator. -/
theorem chainOp_rungOp (σ : ST) :
    chainOp (List.finRange (HubbardLCU.NT x)) (fun i => rungOp x σ i) = selOp x σ := by
  refine LinearMap.ext fun z => ?_
  exact chainOp_finRange_family (fun i : Fin (HubbardLCU.NT x) => rungOp x σ i)
    (fun m => selPart x σ m z)
    (fun j => by
      rw [selPart_succ x σ (j : ℕ) j.isLt]
      rfl)

/-- The ordered rung pass list (at the literal counter values) is the SELECT
operator. -/
theorem chainOp_rungG (τ : ST) :
    chainOp (List.range (HubbardLCU.NT x)) (fun k => rungOp x τ (lCell x hx k))
      = selOp x τ := by
  have h := chainOp_range_of_get (List.finRange (HubbardLCU.NT x))
    (fun k => rungOp x τ (lCell x hx k)) (fun i => rungOp x τ i) (fun j hj => by
      have hjn : j < HubbardLCU.NT x := by rwa [List.length_finRange] at hj
      have hget : (List.finRange (HubbardLCU.NT x)).get ⟨j, hj⟩
          = (⟨j, hjn⟩ : Fin (HubbardLCU.NT x)) := by
        simp [List.get_eq_getElem, List.getElem_finRange]
      rw [hget, lCell_eq_mk x hx hjn])
  rw [List.length_finRange] at h
  exact h.trans (chainOp_rungOp x τ)

/-- The rung transformer acts as one conjugation by the rung operator: the
sign-gate conjugation around the letter suffix family, collapsed through
`wpSuffix_zero_op_conj` and the letter chain bridge. -/
theorem rungT_op (k : ℕ) (A : Assn STc (QubitCells (WL x))) (σ : STc) :
    (rungT x hx k A).op σ
      = LinearMap.adjoint (rungOp x (coef σ) (lCell x hx k)) ∘ₗ A.op σ ∘ₗ
          rungOp x (coef σ) (lCell x hx k) := by
  have h1 : (rungT x hx k A).op σ
      = LinearMap.adjoint (sgnL x (coef σ) (lCell x hx k)) ∘ₗ
          (wpSuffix (letterT x hx k) (2 ^ x) A 0).op σ ∘ₗ
          sgnL x (coef σ) (lCell x hx k) :=
    Assn.unitaryPre_const_op (wpSuffix (letterT x hx k) (2 ^ x) A 0)
      (Reg.single (aC x (lCell x hx k)))
      (fun σ' => singleGate (QubitCells (WL x)) (aC x (lCell x hx k))
        (sgnGate (cf x (coef σ') (lCell x hx k)))) σ
  have h2 : (wpSuffix (letterT x hx k) (2 ^ x) A 0).op σ
      = LinearMap.adjoint (chainOp (List.range (2 ^ x)) (letterG x hx k)) ∘ₗ
          A.op σ ∘ₗ chainOp (List.range (2 ^ x)) (letterG x hx k) :=
    wpSuffix_zero_op_conj (letterT x hx k) (2 ^ x) A (letterG x hx k) σ
      (fun m _ A' => letterT_op x hx k m A' σ)
  rw [h1, h2, chainOp_letterG x hx k,
    show rungOp x (coef σ) (lCell x hx k)
      = ctrlChain x (lCell x hx k) ∘ₗ sgnL x (coef σ) (lCell x hx k) from rfl,
    LinearMap.adjoint_comp]
  simp only [LinearMap.comp_assoc]

/-- The literal-`k` backward transformer of one UNPREPARE pass: (Ax-Uni) at
the Givens pair of the reversed position `N - 2 - k`, the inverse angle read
from the coefficients. -/
noncomputable def unprepT (k : ℕ) (A : Assn STc (QubitCells (WL x))) :
    Assn STc (QubitCells (WL x)) :=
  A.unitaryPre (RegExpr.const (prepReg x (jCell x hx (HubbardLCU.NT x - 2 - k))))
    (fun σ => pairGate (D := QubitCells (WL x))
      (aC x (jA x (jCell x hx (HubbardLCU.NT x - 2 - k))))
      (aC x (jB x (jCell x hx (HubbardLCU.NT x - 2 - k))))
      (jA_ne_jB x (jCell x hx (HubbardLCU.NT x - 2 - k)))
      (givens (-(ang x hx (coef σ)
        ((jCell x hx (HubbardLCU.NT x - 2 - k) : Fin (HubbardLCU.NT x - 1)) : ℕ)
        (jA_lt x (jCell x hx (HubbardLCU.NT x - 2 - k)))))))

/-- The inverse Givens gate at a `Fin` position (the `unprepChain` lambda,
named). -/
noncomputable def unprepGF (τ : ST) (j : Fin (HubbardLCU.NT x - 1)) :
    EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  regLift (prepReg x j)
    ((pairGate (D := QubitCells (WL x)) (aC x (jA x j)) (aC x (jB x j))
      (jA_ne_jB x j) (givens (-(ang x hx τ (j : ℕ) (jA_lt x j))))) :
      TSpace (QubitCells (WL x)) (prepReg x j).toFun →ₗ[ℂ] _)

/-- The UNPREPARE pass operator at the literal counter value. -/
noncomputable def unprepG (τ : ST) (k : ℕ) :
    EndM (QubitCells (WL x)) (univ : Finset (WL x)) :=
  unprepGF x hx τ (jCell x hx (HubbardLCU.NT x - 2 - k))

theorem unprepT_op (k : ℕ) (A : Assn STc (QubitCells (WL x))) (σ : STc) :
    (unprepT x hx k A).op σ
      = LinearMap.adjoint (unprepG x hx (coef σ) k) ∘ₗ A.op σ ∘ₗ
          unprepG x hx (coef σ) k :=
  Assn.unitaryPre_const_op A (prepReg x (jCell x hx (HubbardLCU.NT x - 2 - k)))
    (fun σ' => pairGate (D := QubitCells (WL x))
      (aC x (jA x (jCell x hx (HubbardLCU.NT x - 2 - k))))
      (aC x (jB x (jCell x hx (HubbardLCU.NT x - 2 - k))))
      (jA_ne_jB x (jCell x hx (HubbardLCU.NT x - 2 - k)))
      (givens (-(ang x hx (coef σ')
        ((jCell x hx (HubbardLCU.NT x - 2 - k) : Fin (HubbardLCU.NT x - 1)) : ℕ)
        (jA_lt x (jCell x hx (HubbardLCU.NT x - 2 - k))))))) σ

/-- The ordered UNPREPARE pass list is the un-preparation chain (the reversed
Givens list: pass `k` holds position `N - 2 - k`). -/
theorem chainOp_unprepG (τ : ST) :
    chainOp (List.range (HubbardLCU.NT x - 1)) (unprepG x hx τ)
      = unprepChain x hx τ := by
  have h := chainOp_range_of_get ((List.finRange (HubbardLCU.NT x - 1)).reverse)
    (unprepG x hx τ) (fun j => unprepGF x hx τ j) (fun j hj => by
      have hjn : j < HubbardLCU.NT x - 1 := by
        rwa [List.length_reverse, List.length_finRange] at hj
      have hj2 : HubbardLCU.NT x - 2 - j < HubbardLCU.NT x - 1 := by
        have := NT_gt_one x hx
        omega
      have hget : ((List.finRange (HubbardLCU.NT x - 1)).reverse).get ⟨j, hj⟩
          = jCell x hx (HubbardLCU.NT x - 2 - j) := by
        rw [jCell_eq_mk x hx hj2]
        refine Fin.ext ?_
        rw [List.get_eq_getElem, List.getElem_reverse, List.getElem_finRange]
        simp only [Fin.val_cast, List.length_finRange]
        omega
      rw [hget]
      rfl)
  rw [List.length_reverse, List.length_finRange] at h
  exact h.trans rfl

/-! ## §3b. The suffix `wp` tower of the circuit -/

/-- wp of the final `X(a₀)` (last gate of UNPREPARE). -/
noncomputable def wpU5 : Assn STc (QubitCells (WL x)) :=
  (vacPost x).unitaryPre (RegExpr.const (Reg.single (aC x (a0 x hx))))
    (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)

/-- wp of the counted inverse-Givens loop of UNPREPARE: the suffix family of
the `unprepT` passes at entry. -/
noncomputable def wpU4 : Assn STc (QubitCells (WL x)) :=
  wpSuffix (unprepT x hx) (HubbardLCU.NT x - 1) (wpU5 x hx) 0

/-- wp of SELECT: the suffix family of the `rungT` passes at entry. -/
noncomputable def wpU3 : Assn STc (QubitCells (WL x)) :=
  wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) 0

/-- wp of the counted Givens loop of PREPARE. -/
noncomputable def wpU2 : Assn STc (QubitCells (WL x)) :=
  wpSuffix (prepT x hx) (HubbardLCU.NT x - 1) (wpU3 x hx) 0

/-- **The folded (Ax-Uni) precondition of the whole LCU circuit.** -/
noncomputable def wpLCU : Assn STc (QubitCells (WL x)) :=
  (wpU2 x hx).unitaryPre (RegExpr.const (Reg.single (aC x (a0 x hx))))
    (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X)

/-! ## §3c. Counter-write insensitivity

Both counter lenses of the widened store keep the coefficient block, so every
transformer preserves counter-write insensitivity — the `hg`/`hY` obligations
of the counted-`wp` rules, discharged through the conjugation displays and
`wpSuffix_op_set`. -/

theorem prepT_op_set (c : CounterLens STc) (hc : ∀ σ v, coef (c.set σ v) = coef σ)
    (k : ℕ) (A : Assn STc (QubitCells (WL x)))
    (hA : ∀ σ v, A.op (c.set σ v) = A.op σ) (σ : STc) (v : ℕ) :
    (prepT x hx k A).op (c.set σ v) = (prepT x hx k A).op σ := by
  rw [prepT_op, prepT_op, hA σ v, hc σ v]

theorem letterT_op_set (c : CounterLens STc) (k m : ℕ)
    (A : Assn STc (QubitCells (WL x)))
    (hA : ∀ σ v, A.op (c.set σ v) = A.op σ) (σ : STc) (v : ℕ) :
    (letterT x hx k m A).op (c.set σ v) = (letterT x hx k m A).op σ := by
  rw [letterT_op, letterT_op, hA σ v]

theorem rungT_op_set (c : CounterLens STc) (hc : ∀ σ v, coef (c.set σ v) = coef σ)
    (k : ℕ) (A : Assn STc (QubitCells (WL x)))
    (hA : ∀ σ v, A.op (c.set σ v) = A.op σ) (σ : STc) (v : ℕ) :
    (rungT x hx k A).op (c.set σ v) = (rungT x hx k A).op σ := by
  rw [rungT_op, rungT_op, hA σ v, hc σ v]

theorem unprepT_op_set (c : CounterLens STc) (hc : ∀ σ v, coef (c.set σ v) = coef σ)
    (k : ℕ) (A : Assn STc (QubitCells (WL x)))
    (hA : ∀ σ v, A.op (c.set σ v) = A.op σ) (σ : STc) (v : ℕ) :
    (unprepT x hx k A).op (c.set σ v) = (unprepT x hx k A).op σ := by
  rw [unprepT_op, unprepT_op, hA σ v, hc σ v]

theorem wpU4_op_set (c : CounterLens STc) (hc : ∀ σ v, coef (c.set σ v) = coef σ)
    (σ : STc) (v : ℕ) : (wpU4 x hx).op (c.set σ v) = (wpU4 x hx).op σ :=
  wpSuffix_op_set (unprepT x hx) (wpU5 x hx) c
    (fun k A hA σ' v' => unprepT_op_set x hx c hc k A hA σ' v')
    (fun _ _ => rfl) 0 σ v

theorem wpU3_op_set (c : CounterLens STc) (hc : ∀ σ v, coef (c.set σ v) = coef σ)
    (σ : STc) (v : ℕ) : (wpU3 x hx).op (c.set σ v) = (wpU3 x hx).op σ :=
  wpSuffix_op_set (rungT x hx) (wpU4 x hx) c
    (fun k A hA σ' v' => rungT_op_set x hx c hc k A hA σ' v')
    (fun σ' v' => wpU4_op_set x hx c hc σ' v') 0 σ v

/-! ## §3d. The loop derivations: one packaged counted-`wp` call per loop -/

/-- The UNPREPARE loop: ONE `countedWpChain_const` call along the `unprepT`
suffix family; the agreement of the store-read body with the literal family
is definitional on the step mask. -/
theorem unprepLoopWp :
    DerivTot (wpU4 x hx)
      (countedProg (CounterLens.fst3 ST) (fun _ => HubbardLCU.NT x - 1)
        (unprepBody x hx))
      (wpU5 x hx) := by
  have h : DerivTot (wpSuffix (unprepT x hx) (HubbardLCU.NT x - 1) (wpU5 x hx) 0)
      (countedProg (CounterLens.fst3 ST) (fun _ => HubbardLCU.NT x - 1)
        (Prog.unitary 2 (unprepRegE x hx) (unprepGateE x hx)))
      ((wpU5 x hx).mask fun σ => (CounterLens.fst3 ST).get σ = HubbardLCU.NT x - 1) :=
    DerivTot.countedWpChain_constSource (CounterLens.fst3 ST)
      (unprepRegE x hx) (unprepGateE x hx) (unprepT x hx) (wpU5 x hx)
      (fun k A hA σ v => unprepT_op_set x hx (CounterLens.fst3 ST)
        (fun _ _ => rfl) k A hA σ v)
      (fun _ _ => rfl)
      (fun σ _ => (prepReg x _).inj)
      (fun k _ σ hget A => by subst hget; rfl)
  exact DerivTot.conseq (Assn.le_refl' _) h
    (Assn.mask_le_of_imp_le fun σ _ => le_rfl)

/-- The sign gate of SELECT rung `k`, as the first half of the masked step
obligation: (Ax-Uni) + on-mask (R-Conseq) via `unitary_stepMask`. -/
theorem sgnStepWp (k : ℕ) :
    DerivTot
      ((wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) k).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < HubbardLCU.NT x)
      (sgnBody x hx)
      ((wpSuffix (letterT x hx k) (2 ^ x)
          (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) (k + 1)) 0).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < HubbardLCU.NT x) := by
  refine DerivTot.unitary_stepMask (sgnRegE x hx) (sgnGateE x hx) fun σ hσ => ?_
  obtain ⟨hget, hkn⟩ := hσ
  rw [Assn.unitaryPre_mask_op, Assn.mask_op_of_pos ⟨hget, hkn⟩,
    wpSuffix_of_lt hkn]
  refine le_of_eq ?_
  subst hget
  rfl

/-- The letter loop of SELECT rung `k`, relativised at the outer step mask:
ONE `countedWpChain` call along the `letterT k` suffix family. -/
theorem letterLoopWp (k : ℕ) :
    DerivTot
      ((wpSuffix (letterT x hx k) (2 ^ x)
          (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) (k + 1)) 0).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < HubbardLCU.NT x)
      (countedProg (CounterLens.snd3 ST) (fun _ => 2 ^ x) (ctrlBody x hx))
      ((wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) (k + 1)).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < HubbardLCU.NT x) := by
  have h : DerivTot
      ((wpSuffix (letterT x hx k) (2 ^ x)
          (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) (k + 1)) 0).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < HubbardLCU.NT x)
      (countedProg (CounterLens.snd3 ST) (fun _ => 2 ^ x)
        (Prog.unitary 2 (ctrlRegE x hx) (ctrlGateE x hx)))
      ((wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) (k + 1)).mask
        fun σ => ((CounterLens.fst3 ST).get σ = k ∧ k < HubbardLCU.NT x)
          ∧ (CounterLens.snd3 ST).get σ = 2 ^ x) :=
    DerivTot.countedWpChainSource (CounterLens.snd3 ST) (ctrlRegE x hx) (ctrlGateE x hx)
      (letterT x hx k)
      (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) (k + 1))
      (fun _ _ => Iff.rfl) (fun _ _ => rfl)
      (fun m A hA σ v => letterT_op_set x hx (CounterLens.snd3 ST) k m A hA σ v)
      (fun σ v => wpSuffix_op_set (rungT x hx) (wpU4 x hx) (CounterLens.snd3 ST)
        (fun k' A hA σ' v' => rungT_op_set x hx (CounterLens.snd3 ST)
          (fun _ _ => rfl) k' A hA σ' v')
        (fun σ' v' => wpU4_op_set x hx (CounterLens.snd3 ST)
          (fun _ _ => rfl) σ' v') (k + 1) σ v)
      (fun σ _ _ => (ctrlReg x _ _).inj)
      (fun m _ σ hφ hget A => by
        obtain ⟨hout, -⟩ := hφ
        subst hget
        subst hout
        rfl)
  exact DerivTot.conseq (Assn.le_refl' _) h
    (Assn.mask_le_mask (fun σ hσ => hσ.1) (fun σ _ => le_rfl))

/-- **One SELECT rung**, as the masked step obligation of the outer counted
loop: the sign-gate step glued to the relativised letter loop by (R-Seq). -/
theorem selStepWp (k : ℕ) :
    DerivTot
      ((wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) k).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < HubbardLCU.NT x)
      (rungBody x hx)
      ((wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) (k + 1)).mask
        fun σ => (CounterLens.fst3 ST).get σ = k ∧ k < HubbardLCU.NT x) :=
  DerivTot.seq (sgnStepWp x hx k) (letterLoopWp x hx k)

/-- SELECT's weighted invariant is preserved at the current outer counter;
the inner source loop reads that same outer counter throughout. -/
theorem selStepWpSource :
    DerivTot
      ((Assn.ofFam (CounterLens.fst3 ST).get
        (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx))).mask
        fun σ => σ.1 < HubbardLCU.NT x)
      (rungBody x hx)
      ((Assn.ofFam (CounterLens.fst3 ST).get
        (fun k => wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) (k + 1))).mask
        fun σ => σ.1 < HubbardLCU.NT x) := by
  let J : ℕ → Assn STc (QubitCells (WL x)) := fun m =>
    Assn.ofFam (CounterLens.fst3 ST).get fun k =>
      wpSuffix (letterT x hx k) (2 ^ x)
        (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) (k + 1)) m
  refine DerivTot.seq (B := (J 0).mask fun σ => σ.1 < HubbardLCU.NT x) ?_ ?_
  · refine DerivTot.unitary_stepMask (sgnRegE x hx) (sgnGateE x hx) fun σ hσ => ?_
    rw [Assn.unitaryPre_mask_op,
      Assn.mask_op_of_pos (φ := fun σ : STc => σ.1 < HubbardLCU.NT x) hσ,
      Assn.ofFam_op]
    simp only [CounterLens.fst3]
    rw [wpSuffix_of_lt hσ]
    change (rungT x hx σ.1 _).op σ ≤
      ((Assn.ofFam (CounterLens.fst3 ST).get _).unitaryPre _ _).op σ
    rw [Assn.unitaryPre_ofFam_op]
    exact le_rfl
  · refine DerivTot.conseq (Assn.le_refl' _)
      (DerivTot.countedWhileSource (CounterLens.snd3 ST) (J := J) (n := 2 ^ x)
        (fun _ _ => Iff.rfl) (fun _ _ => rfl) ?_ ?_ ?_) ?_
    · intro m σ v
      change (wpSuffix (letterT x hx σ.1) (2 ^ x)
        (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) (σ.1 + 1)) m).op
          ((CounterLens.snd3 ST).set σ v) = _
      apply wpSuffix_op_set (letterT x hx σ.1) _ (CounterLens.snd3 ST)
        (fun k A hA σ' v' => letterT_op_set x hx (CounterLens.snd3 ST) σ.1 k A hA σ' v')
      intro σ' v'
      exact wpSuffix_op_set (rungT x hx) (wpU4 x hx) (CounterLens.snd3 ST)
        (fun k A hA τ w => rungT_op_set x hx (CounterLens.snd3 ST)
          (fun _ _ => rfl) k A hA τ w)
        (fun τ w => wpU4_op_set x hx (CounterLens.snd3 ST) (fun _ _ => rfl) τ w)
        (σ.1 + 1) σ' v'
    · refine DerivTot.unitary_stepMask (ctrlRegE x hx) (ctrlGateE x hx) fun σ hσ => ?_
      rw [Assn.unitaryPre_mask_op,
        Assn.mask_op_of_pos (φ := fun σ : STc => σ.1 < HubbardLCU.NT x ∧
          (CounterLens.snd3 ST).get σ < 2 ^ x) hσ,
        Assn.ofFam_op]
      simp only [J, Assn.ofFam_op, CounterLens.snd3, CounterLens.fst3]
      have hm : σ.2.1 < 2 ^ x := hσ.2
      rw [wpSuffix_of_lt hm]
      rw [Assn.unitaryPre_ofFam_op]
      rw [Assn.unitaryPre_ofFam_op]
      exact le_rfl
    · intro k
      exact DerivTot.unitary_identity_mask (ctrlRegE x hx) (ctrlGateE x hx)
        (fun σ _ => (ctrlReg x _ _).inj)
    · apply Assn.mask_le_mask (fun _ h => h.1)
      intro σ _
      simp only [J, Assn.ofFam_op, CounterLens.fst3, wpSuffix_full]
      exact le_rfl

/-- The SELECT loop: ONE `countedWpBody_const` call along the `rungT` suffix
family, its steps the `selStepWp` rungs. -/
theorem selLoopWp : DerivTot (wpU3 x hx) (selProg x hx) (wpU4 x hx) := by
  have h : DerivTot (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) 0)
      (countedProg (CounterLens.fst3 ST) (fun _ => HubbardLCU.NT x) (rungBody x hx))
      ((wpU4 x hx).mask fun σ => (CounterLens.fst3 ST).get σ = HubbardLCU.NT x) :=
    DerivTot.countedWpBody_constSource (CounterLens.fst3 ST) (rungT x hx) (wpU4 x hx)
      (fun k A hA σ v => rungT_op_set x hx (CounterLens.fst3 ST)
        (fun _ _ => rfl) k A hA σ v)
      (fun σ v => wpU4_op_set x hx (CounterLens.fst3 ST) (fun _ _ => rfl) σ v)
      (selStepWpSource x hx)
      (fun k => rungIdentity x hx _ (fun _ _ => Iff.rfl))
  exact DerivTot.conseq (Assn.le_refl' _) h
    (Assn.mask_le_of_imp_le fun σ _ => le_rfl)

/-- The PREPARE loop: ONE `countedWpChain_const` call along the `prepT`
suffix family. -/
theorem prepLoopWp :
    DerivTot (wpU2 x hx)
      (countedProg (CounterLens.fst3 ST) (fun _ => HubbardLCU.NT x - 1)
        (prepBody x hx))
      (wpU3 x hx) := by
  have h : DerivTot (wpSuffix (prepT x hx) (HubbardLCU.NT x - 1) (wpU3 x hx) 0)
      (countedProg (CounterLens.fst3 ST) (fun _ => HubbardLCU.NT x - 1)
        (Prog.unitary 2 (prepRegE x hx) (prepGateE x hx)))
      ((wpU3 x hx).mask fun σ => (CounterLens.fst3 ST).get σ = HubbardLCU.NT x - 1) :=
    DerivTot.countedWpChain_constSource (CounterLens.fst3 ST)
      (prepRegE x hx) (prepGateE x hx) (prepT x hx) (wpU3 x hx)
      (fun k A hA σ v => prepT_op_set x hx (CounterLens.fst3 ST)
        (fun _ _ => rfl) k A hA σ v)
      (fun σ v => wpU3_op_set x hx (CounterLens.fst3 ST) (fun _ _ => rfl) σ v)
      (fun σ _ => (prepReg x _).inj)
      (fun k _ σ hget A => by subst hget; rfl)
  exact DerivTot.conseq (Assn.le_refl' _) h
    (Assn.mask_le_of_imp_le fun σ _ => le_rfl)

/-- **PREPARE backward**: the `X(a₀)` (Ax-Uni), then the counted Givens
loop. -/
theorem prepWpDeriv : DerivTot (wpLCU x hx) (prepProg x hx) (wpU3 x hx) :=
  DerivTot.seq
    (DerivTot.unitary (RegExpr.const (Reg.single (aC x (a0 x hx))))
      (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X) (wpU2 x hx))
    (prepLoopWp x hx)

/-- **UNPREPARE backward**: the counted inverse-Givens loop, then the
`X(a₀)` (Ax-Uni). -/
theorem unprepWpDeriv : DerivTot (wpU4 x hx) (unprepProg x hx) (vacPost x) :=
  DerivTot.seq (unprepLoopWp x hx)
    (DerivTot.unitary (RegExpr.const (Reg.single (aC x (a0 x hx))))
      (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X) (vacPost x))

/-- The circuit part of the derivation: the three fragments glued by (R-Seq),
each loop ONE packaged counted-`wp` call. -/
theorem lcuWpDeriv : DerivTot (wpLCU x hx) (lcuProg x hx) (vacPost x) :=
  DerivTot.seq (prepWpDeriv x hx)
    (DerivTot.seq (selLoopWp x hx) (unprepWpDeriv x hx))

/-! ## §4. The folded precondition, displayed as one conjugation -/

theorem wpU5_op (σ : STc) :
    (wpU5 x hx).op σ
      = LinearMap.adjoint (xLift x hx) ∘ₗ ancZeroEff x ∘ₗ xLift x hx :=
  Assn.unitaryPre_const_op (vacPost x) (Reg.single (aC x (a0 x hx)))
    (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X) σ

theorem wpU4_op (σ : STc) :
    (wpU4 x hx).op σ
      = LinearMap.adjoint (unprepChain x hx (coef σ)) ∘ₗ (wpU5 x hx).op σ ∘ₗ
          unprepChain x hx (coef σ) := by
  refine (wpSuffix_zero_op_conj (unprepT x hx) (HubbardLCU.NT x - 1) (wpU5 x hx)
    (unprepG x hx (coef σ)) σ (fun j _ A => unprepT_op x hx j A σ)).trans ?_
  rw [chainOp_unprepG x hx (coef σ)]

theorem wpU3_op (σ : STc) :
    (wpU3 x hx).op σ
      = LinearMap.adjoint (selOp x (coef σ)) ∘ₗ (wpU4 x hx).op σ ∘ₗ
          selOp x (coef σ) := by
  refine (wpSuffix_zero_op_conj (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx)
    (fun k => rungOp x (coef σ) (lCell x hx k)) σ
    (fun k _ A => rungT_op x hx k A σ)).trans ?_
  rw [chainOp_rungG x hx (coef σ)]

theorem wpU2_op (σ : STc) :
    (wpU2 x hx).op σ
      = LinearMap.adjoint (prepChain x hx (coef σ)) ∘ₗ (wpU3 x hx).op σ ∘ₗ
          prepChain x hx (coef σ) := by
  refine (wpSuffix_zero_op_conj (prepT x hx) (HubbardLCU.NT x - 1) (wpU3 x hx)
    (prepG x hx (coef σ)) σ (fun j _ A => prepT_op x hx j A σ)).trans ?_
  rw [chainOp_prepG x hx (coef σ)]

/-- **The wp display**: the folded (Ax-Uni) precondition of the whole circuit
is the single conjugation `W† (∣0…0⟩⟨0…0∣_a ⊗ 1) W` by the circuit operator
at the stored coefficients. -/
theorem wpLCU_op (σ : STc) :
    (wpLCU x hx).op σ
      = LinearMap.adjoint (lcuOp x hx (coef σ)) ∘ₗ ancZeroEff x ∘ₗ
          lcuOp x hx (coef σ) := by
  have h1 : (wpLCU x hx).op σ
      = LinearMap.adjoint (xLift x hx) ∘ₗ (wpU2 x hx).op σ ∘ₗ xLift x hx :=
    Assn.unitaryPre_const_op (wpU2 x hx) (Reg.single (aC x (a0 x hx)))
      (fun _ => singleGate (QubitCells (WL x)) (aC x (a0 x hx)) X) σ
  rw [h1, wpU2_op x hx σ, wpU3_op x hx σ, wpU4_op x hx σ, wpU5_op x hx σ,
    show lcuOp x hx (coef σ)
      = ((xLift x hx ∘ₗ unprepChain x hx (coef σ)) ∘ₗ selOp x (coef σ)) ∘ₗ
          (prepChain x hx (coef σ) ∘ₗ xLift x hx) from rfl]
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_comp]
  simp only [LinearMap.comp_assoc]

/-! ## §5. The (R-Conseq) entailment and the triple -/

/-- **The conseq entailment**: under the mask `λ(σ) > 0`, the effect
`1_a ⊗ λ⁻² H†H` entails (Ax-Init)'s transformer of the folded circuit
precondition — the vacuum block of `W† P₀ W` *is* `λ⁻² H†H` by the
block-encoding identity. -/
theorem succPre_le_init :
    succPre x hx ≤ (wpLCU x hx).initPre fun _ : STc => ancS x := by
  intro σ
  by_cases hlam : 0 < lam x (coef σ)
  · rw [show (succPre x hx).op σ = sysLift (L₂ := AncL x) (succBlock x (coef σ)) from
      Assn.mask_op_of_pos hlam]
    refine le_of_eq ?_
    have hinit : (((wpLCU x hx).initPre fun _ : STc => ancS x)).op σ
        = sysLift (L₂ := AncL x)
            (LinearMap.adjoint (sysEmb x) ∘ₗ (wpLCU x hx).op σ ∘ₗ sysEmb x) :=
      initPre_ancCells_op (L₁ := SysL x) (L₂ := AncL x) (wpLCU x hx) σ
    rw [hinit, wpLCU_op x hx σ]
    refine congrArg _ ?_
    rw [← succBlock_eq_conj x hx (coef σ) hlam,
      show ancZeroEff x = sysEmb x ∘ₗ LinearMap.adjoint (sysEmb x) from rfl]
    simp only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, LinearMap.comp_assoc]
  · exact Assn.op_zero_le (Assn.mask_op_of_neg hlam)

/-- **The LCU success triple**, derived in the printed system
((Ax-Init) + (Ax-Uni) + (Ax-Ass) + (R-Seq) + (R-Conseq) + (R-Loop-tot),
the loops through the counted-`wp` layer):

```
{ (1_a ⊗ λ⁻²H†H).mask (λ(σ) > 0) }  q̄_a := ∣0…0⟩ ; lcuProg  { ∣0…0⟩⟨0…0∣_a ⊗ 1 } .
```
-/
theorem lcuSuccessDeriv :
    DerivTot (succPre x hx) (lcuInitProg x hx) (vacPost x) :=
  DerivTot.conseq (succPre_le_init x hx)
    (DerivTot.seq (DerivTot.initProg _ (wpLCU x hx)) (lcuWpDeriv x hx))
    (Assn.le_refl' _)

/-- **Soundness**: over every input ρ, the expected value of
`1_a ⊗ λ⁻²H†H` (where `λ(σ) > 0`) lower-bounds the probability that the
ancilla block reads all-zero after `init ; prep ; select ; unprep`. -/
theorem lcuSuccessValid :
    validTot (succPre x hx) (lcuInitProg x hx) (vacPost x) :=
  (lcuSuccessDeriv x hx).sound

/-! ## §6. Tightness of the reading -/

/-- At the intended pure input `∣0⟩_a ⊗ ψ` the precondition expectation is
exactly `λ⁻²‖Hψ‖²` — by `effect_reading` this is also the exact success
probability in the output state, so the triple is tight. -/
theorem succPre_expect_pure (σ : STc) (hlam : 0 < lam x (coef σ))
    (ψ : HS (QubitCells (SysL x)) (univ : Finset (SysL x))) :
    expectE (succPre x hx).op ⟨σ, PDensity.pure (sysEmb x ψ)⟩
      = ENNReal.ofReal ((lam x (coef σ))⁻¹ ^ 2
          * ‖hubbardOp x (coef σ).1 (coef σ).2 ψ‖ ^ 2) := by
  rw [expectE_pure]
  congr 1
  rw [show (succPre x hx).op σ = sysLift (L₂ := AncL x) (succBlock x (coef σ)) from
    Assn.mask_op_of_pos hlam,
    show sysEmb x ψ = ancEmbed (L₁ := SysL x) (anc0 x) ψ from rfl,
    inner_emb_sysLift,
    show succBlock x (coef σ) = (((lam x (coef σ))⁻¹ ^ 2 : ℝ) : ℂ) •
      (LinearMap.adjoint (hubbardOp x (coef σ).1 (coef σ).2) ∘ₗ
        hubbardOp x (coef σ).1 (coef σ).2) from rfl,
    LinearMap.smul_apply, inner_smul_right, LinearMap.comp_apply,
    LinearMap.adjoint_inner_right]
  rw [show (⟪hubbardOp x (coef σ).1 (coef σ).2 ψ,
        hubbardOp x (coef σ).1 (coef σ).2 ψ⟫ : ℂ)
      = ((‖hubbardOp x (coef σ).1 (coef σ).2 ψ‖ ^ 2 : ℝ) : ℂ) from by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hubbardOp x (coef σ).1 (coef σ).2 ψ),
      RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-! ## §7. Non-vacuity: an explicit store and input with positive expectation -/

/-- The `±1` weight of a `Z`-string on a computational pattern. -/
def zsC (S : Finset (SysL x)) (g : SysL x → Bool) : ℂ :=
  ∏ k ∈ S, (if g k then (-1 : ℂ) else 1)

theorem zsC_sq (S : Finset (SysL x)) (g : SysL x → Bool) :
    zsC x S g * zsC x S g = 1 := by
  rw [zsC, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun k _ => by split_ifs <;> norm_num

theorem zsC_cases (S : Finset (SysL x)) (g : SysL x → Bool) :
    zsC x S g = 1 ∨ zsC x S g = -1 :=
  mul_self_eq_one_iff.mp (zsC_sq x S g)

theorem prod_symmDiff_sq_one (A B : Finset (SysL x)) (f : SysL x → ℂ)
    (hf : ∀ k, f k * f k = 1) :
    (∏ k ∈ symmDiff A B, f k) = (∏ k ∈ A, f k) * (∏ k ∈ B, f k) := by
  have hsq : (∏ k ∈ A ∩ B, f k) * (∏ k ∈ A ∩ B, f k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => hf k
  have hsd : (∏ k ∈ symmDiff A B, f k) * (∏ k ∈ A ∩ B, f k) = ∏ k ∈ A ∪ B, f k := by
    rw [← Finset.prod_union (Finset.disjoint_left.mpr fun a ha hb => by
      rw [Finset.mem_symmDiff] at ha
      rw [Finset.mem_inter] at hb
      tauto)]
    congr 1
    ext a
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]
    tauto
  calc (∏ k ∈ symmDiff A B, f k)
      = ((∏ k ∈ symmDiff A B, f k) * (∏ k ∈ A ∩ B, f k)) * (∏ k ∈ A ∩ B, f k) := by
        rw [mul_assoc, hsq, mul_one]
    _ = (∏ k ∈ A ∪ B, f k) * (∏ k ∈ A ∩ B, f k) := by rw [hsd]
    _ = (∏ k ∈ A, f k) * (∏ k ∈ B, f k) := Finset.prod_union_inter

/-- At `t = 0` the Hamiltonian is diagonal: on a computational-basis state it
acts by the interaction weight of the stored pattern. -/
theorem hubbard_diag (g : SysL x → Bool) :
    hubbardOp x 0 1 (deltav (QubitCells (SysL x)) (qbIdx (SysL x) g))
      = (∑ j : Fin (nPairs x), (4⁻¹ : ℂ) *
          ((1 - zsC x (nSet x (pL x j)) g) * (1 - zsC x (nSet x (pR x j)) g))) •
        deltav (QubitCells (SysL x)) (qbIdx (SysL x) g) := by
  have h0 : hubbardOp x 0 1
      = ∑ j : Fin (nPairs x), numOp x (pL x j) ∘ₗ numOp x (pR x j) := by
    show (-((0 : ℝ) : ℂ)) • _ + ((1 : ℝ) : ℂ) • _ = _
    norm_num
  rw [h0, LinearMap.sum_apply]
  have hpair : ∀ j : Fin (nPairs x),
      (numOp x (pL x j) ∘ₗ numOp x (pR x j))
          (deltav (QubitCells (SysL x)) (qbIdx (SysL x) g))
        = ((4⁻¹ : ℂ) *
            ((1 - zsC x (nSet x (pL x j)) g) * (1 - zsC x (nSet x (pR x j)) g))) •
            deltav (QubitCells (SysL x)) (qbIdx (SysL x) g) := by
    intro j
    rw [numOp_pair_eq x (pL x j) (pR x j)]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [show zNum x (pL x j) = pauliString (zOn (nSet x (pL x j))) from rfl,
      show zNum x (pR x j) = pauliString (zOn (nSet x (pR x j))) from rfl,
      pauliString_zOn_deltav, pauliString_zOn_deltav, pauliString_zOn_deltav,
      show (∏ k ∈ symmDiff (nSet x (pL x j)) (nSet x (pR x j)),
          (if g k then (-1 : ℂ) else 1))
        = zsC x (nSet x (pL x j)) g * zsC x (nSet x (pR x j)) g from
        prod_symmDiff_sq_one x _ _ _ fun k => by split_ifs <;> norm_num]
    rw [smul_smul, smul_smul, smul_smul, ← sub_smul, ← sub_smul, ← add_smul]
    congr 1
    rw [zsC, zsC]
    ring
  rw [Finset.sum_congr rfl fun j _ => hpair j, ← Finset.sum_smul]

include hx in
theorem nPairs_pos : 0 < nPairs x := by
  have h1 : 1 < 2 ^ x := Nat.one_lt_two_pow_iff.mpr (by omega)
  show 0 < 2 ^ x - 1
  omega

include hx in
/-- The one-norm at the store `(0, 1)` is positive: the type-2 interaction
coefficient of pair `0` is `1/4`. -/
theorem lam_zero_one_pos : 0 < lam x ((0 : ℝ), (1 : ℝ)) := by
  set i₀ : Fin (HubbardLCU.NT x) :=
    (tIdx x).symm (⟨0, nPairs_pos x hx⟩, ⟨2, by norm_num⟩) with hi₀
  have hcf : cf x ((0 : ℝ), (1 : ℝ)) i₀ = 1 / 4 := by
    rw [cf, hi₀, Equiv.apply_symm_apply]
    simp [termCoef]
  refine lt_of_lt_of_le ?_
    (Finset.single_le_sum (f := fun i => |cf x ((0 : ℝ), (1 : ℝ)) i|)
      (fun i _ => abs_nonneg _) (mem_univ i₀))
  rw [hcf]
  norm_num

theorem fSet_zero_eq (h20 : 0 < 2 ^ x) : fSet x ⟨0, h20⟩ = ∅ :=
  Finset.eq_empty_of_forall_notMem fun k hk => by
    have h : (k : ℕ) < 0 := lt_of_mem_fSet hk
    exact absurd h (Nat.not_lt_zero _)

theorem fSet_one_subset (h1x : 1 < 2 ^ x) (k : Fin (2 ^ x))
    (hk : k ∈ fSet x ⟨1, h1x⟩) : k = ⟨0, by omega⟩ := by
  have h : (k : ℕ) < 1 := lt_of_mem_fSet hk
  refine Fin.ext ?_
  show (k : ℕ) = 0
  omega

/-- **Non-vacuity**: at the explicit widened store (counters `0`,
`(t, U) = (0, 1)`) there is an explicit computational-basis input
`∣0⟩_a ⊗ ∣g⟩` on which the precondition expectation is strictly positive (the
pattern `g` doubly occupies the first adjacent pair, so `‖H∣g⟩‖ ≥ 1` while
`λ > 0`). -/
theorem succPre_witness :
    ∃ g : SysL x → Bool,
      0 < expectE (succPre x hx).op
        ⟨((0 : ℕ), (0 : ℕ), ((0 : ℝ), (1 : ℝ))),
          PDensity.pure (sysEmb x (deltav (QubitCells (SysL x)) (qbIdx (SysL x) g)))⟩ := by
  have h20 : 0 < 2 ^ x := pow_pos (by norm_num) x
  have h1x : 1 < 2 ^ x := Nat.one_lt_two_pow_iff.mpr (by omega)
  set c0 : SysL x := ⟨0, h20⟩ with hc0
  set c1 : SysL x := ⟨1, h1x⟩ with hc1
  have hc01 : c0 ≠ c1 := by
    intro hc
    have := congrArg Fin.val hc
    simp [hc0, hc1] at this
  have hj0L : pL x ⟨0, nPairs_pos x hx⟩ = c0 := Fin.ext rfl
  have hj0R : pR x ⟨0, nPairs_pos x hx⟩ = c1 := Fin.ext rfl
  have hnL : nSet x c0 = {c0} := by
    rw [nSet, fSet_zero_eq x h20]
    rfl
  -- choose the pattern according to the (unknown) flip set of mode 1
  obtain ⟨g, hgL, hgR⟩ :
      ∃ g : SysL x → Bool,
        zsC x (nSet x c0) g = -1 ∧ zsC x (nSet x c1) g = -1 := by
    by_cases hmem : c0 ∈ fSet x c1
    · -- `F(1) = {0}`: occupy mode 0 only
      have hf1 : fSet x c1 = {c0} :=
        Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun k hk => fSet_one_subset x h1x k hk⟩
      refine ⟨fun s => if s = c0 then true else false, ?_, ?_⟩
      · rw [hnL, zsC, Finset.prod_singleton, if_pos rfl]
        norm_num
      · rw [nSet, hf1, zsC,
          Finset.prod_insert (Finset.notMem_singleton.mpr (Ne.symm hc01)),
          Finset.prod_singleton, if_neg (Ne.symm hc01), if_pos rfl]
        norm_num
    · -- `F(1) = ∅`: occupy both modes of the pair
      have hf1 : fSet x c1 = ∅ :=
        Finset.eq_empty_of_forall_notMem fun k hk => by
          have hk0 := fSet_one_subset x h1x k hk
          rw [hk0] at hk
          exact hmem hk
      refine ⟨fun s => if s = c0 then true else if s = c1 then true else false, ?_, ?_⟩
      · rw [hnL, zsC, Finset.prod_singleton, if_pos rfl]
        norm_num
      · rw [nSet, hf1, Finset.insert_empty, zsC, Finset.prod_singleton,
          if_neg (Ne.symm hc01), if_pos rfl]
        norm_num
  -- the pair-0 interaction weight is `1`, all others are nonnegative
  have hq0 : (4⁻¹ : ℂ) *
      ((1 - zsC x (nSet x (pL x ⟨0, nPairs_pos x hx⟩)) g) *
        (1 - zsC x (nSet x (pR x ⟨0, nPairs_pos x hx⟩)) g)) = 1 := by
    rw [hj0L, hj0R, hgL, hgR]
    norm_num
  have hqre : ∀ j : Fin (nPairs x),
      0 ≤ ((4⁻¹ : ℂ) * ((1 - zsC x (nSet x (pL x j)) g) *
        (1 - zsC x (nSet x (pR x j)) g))).re := by
    intro j
    rcases zsC_cases x (nSet x (pL x j)) g with h1 | h1 <;>
      rcases zsC_cases x (nSet x (pR x j)) g with h2 | h2 <;>
        rw [h1, h2] <;> norm_num
  have hsum : (1 : ℝ) ≤ (∑ j : Fin (nPairs x), (4⁻¹ : ℂ) *
      ((1 - zsC x (nSet x (pL x j)) g) * (1 - zsC x (nSet x (pR x j)) g))).re := by
    rw [Complex.re_sum]
    calc (1 : ℝ)
        = ((4⁻¹ : ℂ) * ((1 - zsC x (nSet x (pL x ⟨0, nPairs_pos x hx⟩)) g) *
            (1 - zsC x (nSet x (pR x ⟨0, nPairs_pos x hx⟩)) g))).re := by
          rw [hq0]
          norm_num
      _ ≤ _ := Finset.single_le_sum (fun j _ => hqre j)
          (mem_univ (⟨0, nPairs_pos x hx⟩ : Fin (nPairs x)))
  -- the Hamiltonian action on the pattern has norm at least `1`
  have hδ : ‖deltav (QubitCells (SysL x)) (qbIdx (SysL x) g)‖ = 1 := by
    refine norm_eq_one_of_inner_self ?_
    have hdd := dv_dot (D := QubitCells (SysL x)) (qbIdx (SysL x) g) (qbIdx (SysL x) g)
    rw [hdd, if_pos rfl]
  have hnormH : (1 : ℝ) ≤ ‖hubbardOp x 0 1 (deltav (QubitCells (SysL x)) (qbIdx (SysL x) g))‖ := by
    rw [hubbard_diag x g, norm_smul, hδ, mul_one]
    exact hsum.trans (Complex.re_le_norm _)
  refine ⟨g, ?_⟩
  rw [succPre_expect_pure x hx ((0 : ℕ), (0 : ℕ), ((0 : ℝ), (1 : ℝ)))
    (lam_zero_one_pos x hx) _]
  refine ENNReal.ofReal_pos.mpr ?_
  refine mul_pos (pow_pos (inv_pos.mpr (lam_zero_one_pos x hx)) 2) ?_
  show 0 < ‖hubbardOp x 0 1 (deltav (QubitCells (SysL x)) (qbIdx (SysL x) g))‖ ^ 2
  nlinarith [hnormH]

end

end Qhl.HubbardLCUSuccess

/-! ## §8. Axiom audit -/

#print axioms Qhl.HubbardLCUSuccess.lcuSuccessDeriv
#print axioms Qhl.HubbardLCUSuccess.lcuSuccessValid
#print axioms Qhl.HubbardLCUSuccess.succPre_expect_pure
#print axioms Qhl.HubbardLCUSuccess.succPre_witness

namespace Qhl.HubbardLCUSuccess.Source
open Qhl.HubbardLCU Qhl.HubbardLCUSuccess Qhl.BravyiKitaev Finset
open scoped ComplexInnerProductSpace ComplexOrder
variable (x : ℕ) (hx : 0 < x)

/-- PREPARE's weakest-precondition loop derived from source rules. -/
theorem prepLoopWp :
    SourceDerivTot (SourceAssertion.ofAssn (wpU2 x hx) (fun _ => True))
      (countedProg (CounterLens.fst3 ST) (fun _ => HubbardLCU.NT x - 1) (prepBody x hx))
      (SourceAssertion.ofAssn (wpU3 x hx) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (SourceDerivTot.countedWpChain (CounterLens.fst3 ST) (HubbardLCU.NT x - 1)
      (fun _ => True) (prepRegE x hx) (prepGateE x hx) (prepT x hx) (wpU3 x hx)
      (fun _ _ => Iff.rfl)
      (fun k A hA σ v => prepT_op_set x hx (CounterLens.fst3 ST)
        (fun _ _ => rfl) k A hA σ v)
      (fun σ v => wpU3_op_set x hx (CounterLens.fst3 ST) (fun _ _ => rfl) σ v)
      (fun _ _ _ => (prepReg x _).inj)
      (fun k _ σ _ hget A => by subst hget; rfl)) ?_
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)

/-- UNPREPARE's weakest-precondition loop derived from source rules. -/
theorem unprepLoopWp :
    SourceDerivTot (SourceAssertion.ofAssn (wpU4 x hx) (fun _ => True))
      (countedProg (CounterLens.fst3 ST) (fun _ => HubbardLCU.NT x - 1) (unprepBody x hx))
      (SourceAssertion.ofAssn (wpU5 x hx) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (SourceDerivTot.countedWpChain (CounterLens.fst3 ST) (HubbardLCU.NT x - 1)
      (fun _ => True) (unprepRegE x hx) (unprepGateE x hx) (unprepT x hx) (wpU5 x hx)
      (fun _ _ => Iff.rfl)
      (fun k A hA σ v => unprepT_op_set x hx (CounterLens.fst3 ST)
        (fun _ _ => rfl) k A hA σ v)
      (fun _ _ => rfl) (fun _ _ _ => (prepReg x _).inj)
      (fun k _ σ _ hget A => by subst hget; rfl)) ?_
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)

/-- Source weakest-precondition preservation through a compound SELECT rung. -/
theorem selectWpStep :
    SourceDerivTot
      (SourceAssertion.ofAssn (Assn.ofFam (CounterLens.fst3 ST).get
        (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx)))
        (fun σ => True ∧ σ.1 < HubbardLCU.NT x))
      (rungBody x hx)
      (SourceAssertion.ofAssn (Assn.ofFam (CounterLens.fst3 ST).get
        (fun k => wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) (k + 1)))
        (fun σ => True ∧ σ.1 < HubbardLCU.NT x)) := by
  let J : ℕ → Assn STc (QubitCells (WL x)) := fun m =>
    Assn.ofFam (CounterLens.fst3 ST).get fun k =>
      wpSuffix (letterT x hx k) (2 ^ x)
        (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) (k + 1)) m
  refine .seq (B := SourceAssertion.ofAssn (J 0)
    (fun σ => True ∧ σ.1 < HubbardLCU.NT x)) ?_ ?_
  · apply SourceDerivTot.unitary_ofAssn (sgnRegE x hx) (sgnGateE x hx)
      _ _ _ _ (fun _ h => h) (fun _ _ => (Reg.single _).inj)
    intro σ hσ
    rw [Assn.ofFam_op]
    simp only [CounterLens.fst3]
    rw [wpSuffix_of_lt hσ.2]
    change (rungT x hx σ.1 _).op σ ≤
      ((Assn.ofFam (CounterLens.fst3 ST).get _).unitaryPre _ _).op σ
    rw [Assn.unitaryPre_ofFam_op]
    exact le_rfl
  · refine .conseq (SourceAssertion.entails_refl _)
      (SourceDerivTot.countedFamily (CounterLens.snd3 ST) (2 ^ x)
        (fun σ => True ∧ σ.1 < HubbardLCU.NT x) J (ctrlBody x hx)
        (fun _ _ => Iff.rfl) ?_ ?_ ?_) ?_
    · intro m σ v
      change (wpSuffix (letterT x hx σ.1) (2 ^ x)
        (wpSuffix (rungT x hx) (HubbardLCU.NT x) (wpU4 x hx) (σ.1 + 1)) m).op
          ((CounterLens.snd3 ST).set σ v) = _
      apply wpSuffix_op_set (letterT x hx σ.1) _ (CounterLens.snd3 ST)
        (fun k A hA σ' v' => letterT_op_set x hx (CounterLens.snd3 ST) σ.1 k A hA σ' v')
      intro σ' v'
      exact wpSuffix_op_set (rungT x hx) (wpU4 x hx) (CounterLens.snd3 ST)
        (fun k A hA τ w => rungT_op_set x hx (CounterLens.snd3 ST)
          (fun _ _ => rfl) k A hA τ w)
        (fun τ w => wpU4_op_set x hx (CounterLens.snd3 ST) (fun _ _ => rfl) τ w)
        (σ.1 + 1) σ' v'
    · apply SourceDerivTot.unitary_ofAssn (ctrlRegE x hx) (ctrlGateE x hx)
        _ _ _ _ (fun _ h => h) (fun _ _ => (ctrlReg x _ _).inj)
      intro σ hσ
      simp only [J, Assn.ofFam_op, CounterLens.snd3, CounterLens.fst3]
      have hm : σ.2.1 < 2 ^ x := hσ.2
      rw [wpSuffix_of_lt hm]
      rw [Assn.unitaryPre_ofFam_op, Assn.unitaryPre_ofFam_op]
      exact le_rfl
    · intro z
      exact SourceDerivTot.unitary_identity (ctrlRegE x hx) (ctrlGateE x hx) _
        (fun _ _ => (ctrlReg x _ _).inj)
    · apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ h => h.1)
      intro σ _
      simp only [J, Assn.ofFam_op, CounterLens.fst3, wpSuffix_full]
      exact le_rfl

/-- SELECT's source weakest-precondition loop. -/
theorem selectWp :
    SourceDerivTot (SourceAssertion.ofAssn (wpU3 x hx) (fun _ => True))
      (selProg x hx) (SourceAssertion.ofAssn (wpU4 x hx) (fun _ => True)) := by
  refine .conseq (SourceAssertion.entails_refl _)
    (SourceDerivTot.countedWpBody (CounterLens.fst3 ST) (HubbardLCU.NT x)
      (fun _ => True) (rungT x hx) (wpU4 x hx) (rungBody x hx)
      (fun _ _ => Iff.rfl)
      (fun k A hA σ v => rungT_op_set x hx (CounterLens.fst3 ST)
        (fun _ _ => rfl) k A hA σ v)
      (fun σ v => wpU4_op_set x hx (CounterLens.fst3 ST) (fun _ _ => rfl) σ v)
      (selectWpStep x hx) (fun _ => HubbardLCU.Source.rungIdentity x hx _ (fun _ _ => Iff.rfl))) ?_
  exact SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial) (fun _ _ => le_rfl)

/-- The source weakest-precondition derivation for the literal entire LCU circuit. -/
theorem lcuWp :
    SourceDerivTot (SourceAssertion.ofAssn (wpLCU x hx) (fun _ => True))
      (lcuProg x hx) (SourceAssertion.ofAssn (vacPost x) (fun _ => True)) := by
  refine .seq (.seq ?_ (prepLoopWp x hx)) (.seq (selectWp x hx) (.seq (unprepLoopWp x hx) ?_))
  · exact SourceDerivTot.unitary_ofAssn _ _ _ _ _ _ (fun _ h => h)
      (fun _ _ => (Reg.single _).inj) (fun _ _ => le_rfl)
  · exact SourceDerivTot.unitary_ofAssn _ _ _ _ _ _ (fun _ h => h)
      (fun _ _ => (Reg.single _).inj) (fun _ _ => le_rfl)

/-- The unmasked physical success observable with the intended separate `λ > 0` condition. -/
noncomputable def successPre : SourceAssertion STc (QubitCells (WL x)) :=
  SourceAssertion.ofAssn
    ⟨fun σ => sysLift (L₂ := AncL x) (succBlock x (coef σ)),
      fun σ => isEffect_sysLift (isEffect_succBlock x hx (coef σ))⟩
    (fun σ => 0 < lam x (coef σ))

/-- Exact LCU success triple, derived only through source constructors and operator inequalities. -/
theorem lcuSuccessDeriv :
    SourceDerivTot (successPre x hx) (lcuInitProg x hx)
      (SourceAssertion.ofAssn (vacPost x) (fun _ => True)) := by
  refine .conseq ?_
    (.seq (.initProg (fun _ => ancS x)
      (SourceAssertion.ofAssn (wpLCU x hx) (fun _ => True))) (lcuWp x hx))
    (SourceAssertion.entails_refl _)
  apply SourceAssertion.entails_ofAssn _ _ _ _ (fun _ _ => trivial)
  intro σ hσ
  have h := succPre_le_init x hx σ
  rw [show (succPre x hx).op σ = sysLift (L₂ := AncL x) (succBlock x (coef σ)) from
    Assn.mask_op_of_pos hσ] at h
  exact h

/-- The separate classical/quantum success precondition encodes to the original effect. -/
theorem successPre_toAssn : (successPre x hx).toAssn = succPre x hx := by
  exact SourceAssertion.toAssn_ofAssn _ _

/-- The original semantic success triple now follows from the genuine source root. -/
theorem lcuSuccessValid : validTot (succPre x hx) (lcuInitProg x hx) (vacPost x) := by
  simpa only [successPre_toAssn, SourceAssertion.toAssn_ofAssn_true] using
    (lcuSuccessDeriv x hx).sound

end Qhl.HubbardLCUSuccess.Source

#print axioms Qhl.HubbardLCUSuccess.Source.lcuSuccessDeriv
#print axioms Qhl.HubbardLCUSuccess.Source.lcuSuccessValid
