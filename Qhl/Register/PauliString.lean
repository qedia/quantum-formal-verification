import Qhl.Register.Qubits
import Qhl.Gate.PauliAlgebra

/-!
# Pauli strings on the labelled qubit world

A *Pauli string* on the all-qubit world `QubitCells L` is a per-site
assignment `P : L → PLetter` of one of the four letters `1, X, Y, Z`, lifted to
the whole world as the composition of the one-site gates `gateAt a (P a).gate`
(`Qhl/Register/Qubits.lean`), one factor per site.  Because each letter sends a
computational basis ket to a unit scalar times a basis ket, a whole string acts
on `deltav` basis states by

* flipping the bit at every `X`/`Y` site (`PLetter.flips`), and
* multiplying by the product of the per-site scalars (`PLetter.ph`):
  `1` for `1`/`X`, the parity sign `(-1)^b` for `Z`, and `i·(-1)^b` for `Y`

— the master action lemma `pauliString_deltav`.  From it:

* `pauliString_zOn_deltav`/`pauliString_xOn_deltav` — pure `Z`-strings are
  diagonal with parity signs, pure `X`-strings flip bits;
* `pauliString_comm_of_disjoint` — strings supported on disjoint site sets
  commute;
* `gateAt_X_comp_Y` (and cyclic) — same-cell letters compose by the
  single-qubit algebra of `Qhl/Gate/PauliAlgebra.lean`, e.g.
  `X_a ∘ Y_a = i • Z_a`;
* `pauliString_comp_self`, `isUnitary_pauliString`, `adjoint_pauliString` —
  every string is an involution, unitary, and self-adjoint.

The classical index bridge is `qbIdx : (L → Bool) → QIdx (QubitCells L) univ`
with the extensionality `qubitEndM_ext`: an operator on the world is determined
by its values on the kets `deltav (qbIdx f)`.
-/

namespace Qhl

open Finset
open scoped ComplexInnerProductSpace

/-! ## The four Pauli letters -/

/-- The four Pauli letters: identity, `X`, `Y`, `Z`. -/
inductive PLetter : Type
  | one : PLetter
  | x : PLetter
  | y : PLetter
  | z : PLetter
  deriving DecidableEq

namespace PLetter

/-- The one-qubit gate of a letter. -/
noncomputable def gate : PLetter → UnitaryOp 𝕢
  | one => 1
  | x => X
  | y => Y
  | z => Z

/-- Whether the letter flips the computational basis bit (`X` and `Y` do). -/
def flips : PLetter → Bool
  | one => false
  | x => true
  | y => true
  | z => false

/-- The unit scalar the letter produces on the basis ket `∣b⟩`:
`X∣b⟩ = ∣¬b⟩`, `Z∣b⟩ = (-1)^b ∣b⟩`, `Y∣b⟩ = i(-1)^b ∣¬b⟩`. -/
def ph : PLetter → Bool → ℂ
  | one, _ => 1
  | x, _ => 1
  | y, b => if b then -Complex.I else Complex.I
  | z, b => if b then -1 else 1

/-- The uniform basis action of a letter: a unit scalar times a basis ket. -/
theorem gate_single (p : PLetter) (b : Bool) :
    (p.gate : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single b 1)
      = p.ph b • EuclideanSpace.single (xor p.flips b) 1 := by
  cases p with
  | one => simp [gate, ph, flips]
  | x => simp [gate, ph, flips, X_single, Bool.true_xor]
  | y => simpa [gate, ph, flips, Bool.true_xor] using Y_single b
  | z => simpa [gate, ph, flips, Bool.false_xor] using Z_single b

/-- Applying a letter twice multiplies the two scalars to `1`: letters are
involutions. -/
theorem ph_mul_ph_flips (p : PLetter) (b : Bool) :
    p.ph b * p.ph (xor p.flips b) = 1 := by
  cases p <;> cases b <;>
    simp [ph, flips, Complex.I_mul_I]

end PLetter

/-! ## The classical index bridge -/

section World

variable (L : Type*) [Fintype L] [DecidableEq L]

/-- A total bit vector read as a classical state of the all-qubit world. -/
def qbIdx (f : L → Bool) : QIdx (QubitCells L) (univ : Finset L) := fun i => f i

variable {L}

/-- Every classical state of the world is `qbIdx` of a total bit vector. -/
theorem qbIdx_eq (k : QIdx (QubitCells L) (univ : Finset L)) :
    qbIdx L (fun i => k ⟨i, mem_univ i⟩) = k := by
  funext i
  exact congrArg k (Subtype.ext rfl)

/-- An operator on the all-qubit world is determined by its values on the
computational basis kets of total bit vectors. -/
theorem qubitEndM_ext {A B : EndM (QubitCells L) (univ : Finset L)}
    (h : ∀ f : L → Bool,
      A (deltav (QubitCells L) (qbIdx L f)) = B (deltav (QubitCells L) (qbIdx L f))) :
    A = B := by
  apply linM_ext
  intro k
  have h2 := h (fun i => k ⟨i, mem_univ i⟩)
  rwa [qbIdx_eq] at h2

end World

/-! ## A scalar slips out of one factor of a product state -/

section ProdV

variable {L : Type*} [DecidableEq L]
variable (D : L → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {W : Finset L}

/-- Scaling one factor of a per-cell product state scales the product state. -/
theorem prodV_update_smulPS (a : L) (ha : a ∈ W) (ψ : ∀ i, EuclideanSpace ℂ (D i))
    (c : ℂ) (v : EuclideanSpace ℂ (D a)) :
    prodV D (W := W) (Function.update ψ a (c • v))
      = c • prodV D (W := W) (Function.update ψ a v) := by
  refine PiLp.ext fun l => ?_
  rw [prodV_apply, PiLp.smul_apply, prodV_apply, smul_eq_mul]
  set i0 : ↥W := ⟨a, ha⟩ with hi0
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0)]
  have e1 : Function.update ψ a (c • v) (i0 : L) (l i0)
      = c * Function.update ψ a v (i0 : L) (l i0) := by
    show Function.update ψ a (c • v) a (l i0) = c * Function.update ψ a v a (l i0)
    rw [Function.update_self, Function.update_self, PiLp.smul_apply, smul_eq_mul]
  have e2 : ∀ i ∈ Finset.univ.erase i0,
      Function.update ψ a (c • v) (i : L) (l i)
        = Function.update ψ a v (i : L) (l i) := fun i hi => by
    have hne : (i : L) ≠ a := fun hc =>
      (Finset.mem_erase.mp hi).1 (Subtype.ext hc)
    rw [Function.update_of_ne hne, Function.update_of_ne hne]
  rw [e1, Finset.prod_congr rfl e2, mul_assoc]

end ProdV

/-! ## One letter on one site of a basis ket -/

section Gate

variable {L : Type*} [Fintype L] [DecidableEq L]

omit [Fintype L] in
/-- Updating one slot of a family of basis kets is the family of the updated
bit vector. -/
theorem update_singleFamily (f : L → Bool) (a : L) (b : Bool) :
    Function.update
        (fun i => (EuclideanSpace.single (f i) 1 :
          EuclideanSpace ℂ (QubitCells L i))) a
        (EuclideanSpace.single b 1)
      = fun i => EuclideanSpace.single (Function.update f a b i) 1 := by
  funext i
  by_cases hi : i = a
  · subst hi
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

/-- A one-site gate whose action on the named basis ket is a scalar times a
basis ket acts on a `deltav` of the world accordingly. -/
theorem gateAt_deltav (a : L) (U : UnitaryOp 𝕢) (f : L → Bool) {c : ℂ} {b : Bool}
    (h : (U : 𝕢 →ₗ[ℂ] 𝕢) (EuclideanSpace.single (f a) 1)
      = c • EuclideanSpace.single b 1) :
    gateAt L a U (deltav (QubitCells L) (qbIdx L f))
      = c • deltav (QubitCells L) (qbIdx L (Function.update f a b)) := by
  have h1 : deltav (QubitCells L) (qbIdx L f)
      = prodV (QubitCells L) (W := univ)
          (fun i => EuclideanSpace.single (f i) 1) :=
    (prodV_single (QubitCells L) f).symm
  rw [h1, gateAt_prodV, h, prodV_update_smulPS (QubitCells L) a (mem_univ a),
    update_singleFamily, prodV_single]
  rfl

/-- A Pauli letter on one site of a basis ket: flip the bit if the letter
flips, and multiply by the letter's scalar at the stored bit. -/
theorem gateAt_letter_deltav (a : L) (p : PLetter) (f : L → Bool) :
    gateAt L a p.gate (deltav (QubitCells L) (qbIdx L f))
      = p.ph (f a) •
          deltav (QubitCells L) (qbIdx L (Function.update f a (xor p.flips (f a)))) :=
  gateAt_deltav a p.gate f (p.gate_single (f a))

end Gate

/-! ## Pauli strings -/

section String

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The composition of the one-site letter gates over a list of sites. -/
noncomputable def stringOn (P : L → PLetter) : List L → EndM (QubitCells L) (univ : Finset L)
  | [] => 1
  | a :: t => gateAt L a (P a).gate ∘ₗ stringOn P t

@[simp]
theorem stringOn_nil (P : L → PLetter) : stringOn P [] = 1 := rfl

theorem stringOn_cons (P : L → PLetter) (a : L) (t : List L) :
    stringOn P (a :: t) = gateAt L a (P a).gate ∘ₗ stringOn P t := rfl

/-- **The Pauli string** of a letter assignment: the composition of all the
one-site letter gates (sites enumerated once each; the order is immaterial by
`pauliString_deltav`). -/
noncomputable def pauliString (P : L → PLetter) : EndM (QubitCells L) (univ : Finset L) :=
  stringOn P (univ : Finset L).toList

/-- The action of a partial string on a basis ket: flip the visited `X`/`Y`
bits, multiply the visited letters' scalars. -/
theorem stringOn_deltav (P : L → PLetter) :
    ∀ l : List L, l.Nodup → ∀ f : L → Bool,
      stringOn P l (deltav (QubitCells L) (qbIdx L f))
        = (∏ k ∈ l.toFinset, (P k).ph (f k)) •
            deltav (QubitCells L)
              (qbIdx L (fun k => if k ∈ l then xor (P k).flips (f k) else f k)) := by
  intro l
  induction l with
  | nil =>
      intro _ f
      have hf : (fun k => if k ∈ ([] : List L) then xor (P k).flips (f k) else f k) = f := by
        funext k
        simp
      rw [hf]
      simp
  | cons a t ih =>
      intro hl f
      have hat : a ∉ t := (List.nodup_cons.mp hl).1
      have ht : t.Nodup := (List.nodup_cons.mp hl).2
      set f' : L → Bool := fun k => if k ∈ t then xor (P k).flips (f k) else f k with hf'
      have hfa : f' a = f a := by
        rw [hf']
        exact if_neg hat
      rw [stringOn_cons, LinearMap.comp_apply, ih ht f, map_smul,
        gateAt_letter_deltav a (P a) f', hfa]
      have hket : Function.update f' a (xor (P a).flips (f a))
          = fun k => if k ∈ a :: t then xor (P k).flips (f k) else f k := by
        funext k
        by_cases hk : k = a
        · subst hk
          rw [Function.update_self, if_pos List.mem_cons_self]
        · rw [Function.update_of_ne hk]
          show (if k ∈ t then xor (P k).flips (f k) else f k) = _
          simp only [List.mem_cons, hk, false_or]
      have hprod : (∏ k ∈ (a :: t).toFinset, (P k).ph (f k))
          = (P a).ph (f a) * ∏ k ∈ t.toFinset, (P k).ph (f k) := by
        rw [List.toFinset_cons,
          Finset.prod_insert (fun hc => hat (List.mem_toFinset.mp hc))]
      rw [hket, smul_smul, hprod, mul_comm ((P a).ph (f a))]

/-- **The master action lemma**: a Pauli string flips the bits at its `X`/`Y`
sites and multiplies by the product of the per-site scalars — the `Z` (and `Y`)
sites contributing parity signs at the stored bits. -/
theorem pauliString_deltav (P : L → PLetter) (f : L → Bool) :
    pauliString P (deltav (QubitCells L) (qbIdx L f))
      = (∏ k, (P k).ph (f k)) •
          deltav (QubitCells L) (qbIdx L (fun k => xor (P k).flips (f k))) := by
  rw [pauliString, stringOn_deltav P _ (Finset.nodup_toList _) f]
  have h1 : (univ : Finset L).toList.toFinset = univ := Finset.toList_toFinset _
  have h2 : (fun k => if k ∈ (univ : Finset L).toList then xor (P k).flips (f k) else f k)
      = fun k => xor (P k).flips (f k) := by
    funext k
    rw [if_pos (Finset.mem_toList.mpr (mem_univ k))]
  rw [h1, h2]

/-! ## Involution, unitarity, self-adjointness -/

/-- A Pauli string composed with itself is the identity. -/
theorem pauliString_comp_self (P : L → PLetter) :
    pauliString P ∘ₗ pauliString P = 1 := by
  refine qubitEndM_ext fun f => ?_
  rw [LinearMap.comp_apply, pauliString_deltav, map_smul, pauliString_deltav,
    smul_smul, Module.End.one_apply]
  have hket : (fun k => xor (P k).flips (xor (P k).flips (f k))) = f := by
    funext k
    cases (P k).flips <;> cases f k <;> rfl
  rw [hket, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun k _ => (P k).ph_mul_ph_flips (f k),
    Finset.prod_const_one, one_smul]

/-- Every partial string is unitary (a composition of one-site gates). -/
theorem isUnitary_stringOn (P : L → PLetter) :
    ∀ l : List L, IsUnitary (stringOn P l)
  | [] => by
      constructor <;>
        simp [stringOn_nil, LinearMap.adjoint_one, Module.End.one_eq_id]
  | a :: t => by
      rw [stringOn_cons]
      exact IsUnitary.comp (isUnitary_gateAt L a (P a).gate) (isUnitary_stringOn P t)

/-- Every Pauli string is unitary. -/
theorem isUnitary_pauliString (P : L → PLetter) : IsUnitary (pauliString P) :=
  isUnitary_stringOn P _

/-- Every Pauli string is self-adjoint (unitary + involution). -/
theorem adjoint_pauliString (P : L → PLetter) :
    LinearMap.adjoint (pauliString P) = pauliString P := by
  have h := (isUnitary_pauliString P).1
  calc LinearMap.adjoint (pauliString P)
      = LinearMap.adjoint (pauliString P) ∘ₗ (pauliString P ∘ₗ pauliString P) := by
        rw [pauliString_comp_self, Module.End.one_eq_id, LinearMap.comp_id]
    _ = (LinearMap.adjoint (pauliString P) ∘ₗ pauliString P) ∘ₗ pauliString P := by
        rw [LinearMap.comp_assoc]
    _ = pauliString P := by
        rw [h, Module.End.one_eq_id, LinearMap.id_comp]

/-! ## Strings on disjoint supports commute -/

/-- Pauli strings whose non-identity letters live on disjoint site sets
commute: neither flips a bit the other's parity signs read. -/
theorem pauliString_comm_of_disjoint (P Q : L → PLetter)
    (h : ∀ k, P k = PLetter.one ∨ Q k = PLetter.one) :
    pauliString P ∘ₗ pauliString Q = pauliString Q ∘ₗ pauliString P := by
  refine qubitEndM_ext fun f => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, pauliString_deltav, map_smul,
    pauliString_deltav, pauliString_deltav, map_smul, pauliString_deltav,
    smul_smul, smul_smul]
  have hket : (fun k => xor (P k).flips (xor (Q k).flips (f k)))
      = fun k => xor (Q k).flips (xor (P k).flips (f k)) := by
    funext k
    cases (P k).flips <;> cases (Q k).flips <;> cases f k <;> rfl
  rw [hket]
  refine congrArg (· • _) ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rcases h k with hk | hk <;> rw [hk] <;>
    simp [PLetter.ph, PLetter.flips, Bool.false_xor, mul_comm]

/-! ## Same-cell letters compose by the single-qubit algebra -/

/-- `X_a ∘ Y_a = i • Z_a` on the world: same-cell letters compose by the
single-qubit multiplication table. -/
theorem gateAt_X_comp_Y (a : L) :
    gateAt L a X ∘ₗ gateAt L a Y = Complex.I • gateAt L a Z := by
  show gateAt L a PLetter.x.gate ∘ₗ gateAt L a PLetter.y.gate
      = Complex.I • gateAt L a PLetter.z.gate
  refine qubitEndM_ext fun f => ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, gateAt_letter_deltav,
    map_smul, smul_smul, Function.update_self, Function.update_idem,
    PLetter.flips, Bool.true_xor, Bool.false_xor, Bool.not_not,
    Function.update_eq_self]
  cases hfa : f a <;> simp [PLetter.ph, Complex.I_mul_I]

/-- `Y_a ∘ Z_a = i • X_a` on the world. -/
theorem gateAt_Y_comp_Z (a : L) :
    gateAt L a Y ∘ₗ gateAt L a Z = Complex.I • gateAt L a X := by
  show gateAt L a PLetter.y.gate ∘ₗ gateAt L a PLetter.z.gate
      = Complex.I • gateAt L a PLetter.x.gate
  refine qubitEndM_ext fun f => ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, gateAt_letter_deltav,
    map_smul, smul_smul, Function.update_self, Function.update_idem,
    PLetter.flips, Bool.true_xor, Bool.false_xor, Bool.not_not,
    Function.update_eq_self]
  cases hfa : f a <;> simp [PLetter.ph, Complex.I_mul_I]

/-- `Z_a ∘ X_a = i • Y_a` on the world. -/
theorem gateAt_Z_comp_X (a : L) :
    gateAt L a Z ∘ₗ gateAt L a X = Complex.I • gateAt L a Y := by
  show gateAt L a PLetter.z.gate ∘ₗ gateAt L a PLetter.x.gate
      = Complex.I • gateAt L a PLetter.y.gate
  refine qubitEndM_ext fun f => ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, gateAt_letter_deltav,
    map_smul, smul_smul, Function.update_self, Function.update_idem,
    PLetter.flips, Bool.true_xor, Bool.false_xor, Bool.not_not,
    Function.update_eq_self]
  cases hfa : f a <;> simp [PLetter.ph, Complex.I_mul_I]

/-! ## Pure `Z`-strings and pure `X`-strings -/

/-- The letter assignment `Z` on `S`, identity elsewhere. -/
def zOn (S : Finset L) : L → PLetter := fun k => if k ∈ S then PLetter.z else PLetter.one

/-- The letter assignment `X` on `S`, identity elsewhere. -/
def xOn (S : Finset L) : L → PLetter := fun k => if k ∈ S then PLetter.x else PLetter.one

/-- A pure `Z`-string is diagonal: it multiplies a basis ket by the parity
sign of the bits stored on its support. -/
theorem pauliString_zOn_deltav (S : Finset L) (f : L → Bool) :
    pauliString (zOn S) (deltav (QubitCells L) (qbIdx L f))
      = (∏ k ∈ S, (if f k then (-1 : ℂ) else 1)) • deltav (QubitCells L) (qbIdx L f) := by
  rw [pauliString_deltav]
  have hket : (fun k => xor ((zOn S k)).flips (f k)) = f := by
    funext k
    by_cases hk : k ∈ S <;> simp [zOn, hk, PLetter.flips]
  have hprod : (∏ k, (zOn S k).ph (f k))
      = ∏ k ∈ S, (if f k then (-1 : ℂ) else 1) := by
    have h1 : ∀ k, (zOn S k).ph (f k)
        = if k ∈ S then (if f k then (-1 : ℂ) else 1) else 1 := fun k => by
      by_cases hk : k ∈ S <;> simp [zOn, hk, PLetter.ph]
    rw [Finset.prod_congr rfl fun k _ => h1 k, Finset.prod_ite_mem,
      Finset.univ_inter]
  rw [hket, hprod]

/-- A pure `X`-string flips the bits on its support (no scalar). -/
theorem pauliString_xOn_deltav (S : Finset L) (f : L → Bool) :
    pauliString (xOn S) (deltav (QubitCells L) (qbIdx L f))
      = deltav (QubitCells L) (qbIdx L (fun k => xor (decide (k ∈ S)) (f k))) := by
  rw [pauliString_deltav]
  have hprod : (∏ k, (xOn S k).ph (f k)) = 1 :=
    Finset.prod_eq_one fun k _ => by
      by_cases hk : k ∈ S <;> simp [xOn, hk, PLetter.ph]
  have hket : (fun k => xor ((xOn S k)).flips (f k))
      = fun k => xor (decide (k ∈ S)) (f k) := by
    funext k
    by_cases hk : k ∈ S <;> simp [xOn, hk, PLetter.flips]
  rw [hprod, hket, one_smul]

end String

end Qhl
