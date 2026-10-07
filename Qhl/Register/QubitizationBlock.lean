import Qhl.Register.Qubitization

/-!
# The phased-walk product operator and its adjoint block

`Qhl/Register/Qubitization.lean` analyses the *iterate* of phased passes on
the embedded block vector (`qspIter`, `qsp_product`).  A backward
(weakest-precondition) computation needs the same walk as an *operator*: the
composite of the pass operators, its action on the embedded vector, and —
the key new fact — its **adjoint block value**

```
E† ((∏ₖ passₖ)† (E v))  =  conj (P_φ(c)) • v ,
```

i.e. the pulled-back vacuum-sector vector of the whole walk is *collinear
with* the block vector, with amplitude the conjugated QSP polynomial entry.
This is what turns the transfer bound into a Löwner-order entailment between
effects: the wp of `∣E v⟩⟨E v∣` through the walk compresses, on the vacuum
sector, to `|P_φ(c)|² ∣v⟩⟨v∣` exactly.

The collinearity is the invariance of the walk plane: each pass maps the
orthocomplement of `span{E v, u₁}` into itself, because `E v` and `u₁` are
recovered from their own pass images by the inverse 2×2 rotation and the pass
preserves inner products (`pass_orth`); the induction over the passes is
`passProd_orth`.

`qspMat_zero_sq` / `qspPoly_zero_even` evaluate the QSP product at block
value `c = 0` and zero angles — the closed instance a non-vacuity witness
uses.

Nothing here names a program or a Hamiltonian (ownership test).
-/

namespace Qhl.Qubitization

open scoped ComplexInnerProductSpace

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [FiniteDimensional ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]

variable (Uop R : H₂ →ₗ[ℂ] H₂) (Ph : ℝ → H₂ →ₗ[ℂ] H₂)

/-! ## §1. The walk product operator -/

/-- The product of the phased passes `k, k+1, …, k+n−1`, pass `k` applied
first — the operator the loop body composes, with the pass window starting at
the loop counter `k`. -/
noncomputable def passProd (φs : ℕ → ℝ) : ℕ → ℕ → (H₂ →ₗ[ℂ] H₂)
  | _, 0 => 1
  | k, n + 1 => passProd φs (k + 1) n ∘ₗ passOp Uop R Ph (φs k)

@[simp]
theorem passProd_zero (φs : ℕ → ℝ) (k : ℕ) : passProd Uop R Ph φs k 0 = 1 := rfl

theorem passProd_succ (φs : ℕ → ℝ) (k n : ℕ) :
    passProd Uop R Ph φs k (n + 1)
      = passProd Uop R Ph φs (k + 1) n ∘ₗ passOp Uop R Ph (φs k) := rfl

/-- The product also grows at the top: the last pass composes on the left. -/
theorem passProd_succ_top (φs : ℕ → ℝ) (k n : ℕ) :
    passProd Uop R Ph φs k (n + 1)
      = passOp Uop R Ph (φs (k + n)) ∘ₗ passProd Uop R Ph φs k n := by
  induction n generalizing k with
  | zero =>
      rw [passProd_succ, passProd_zero, passProd_zero, Nat.add_zero,
        Module.End.one_eq_id, LinearMap.id_comp, LinearMap.comp_id]
  | succ n ih =>
      rw [passProd_succ, ih (k + 1), passProd_succ, LinearMap.comp_assoc,
        show k + 1 + n = k + (n + 1) from by omega]

variable (E : H₁ →ₗ[ℂ] H₂) (v : H₁)

/-- On the embedded block vector the walk product from `0` is the iterate. -/
theorem passProd_emb (φs : ℕ → ℝ) (m : ℕ) :
    passProd Uop R Ph φs 0 m (E v) = qspIter E Uop R Ph v φs m := by
  induction m with
  | zero => exact Module.End.one_apply _
  | succ m ih =>
      rw [passProd_succ_top, qspIter_succ, LinearMap.comp_apply, ih, Nat.zero_add]

/-! ## §2. The invariance of the walk plane's orthocomplement -/

variable {E Uop R Ph v}
variable {c : ℝ}

/-- One phased pass maps the orthocomplement of the walk plane
`span{E v, u₁}` into itself: `E v` and `u₁` are recovered from their own pass
images by the inverse 2×2 rotation, and the pass preserves inner products. -/
theorem pass_orth (h : IsQubitization E Uop R Ph v c) (hc : c ^ 2 < 1)
    (hpass : ∀ φ, IsIsometryOp (passOp Uop R Ph φ)) (φ : ℝ) {z : H₂}
    (h0 : (⟪E v, z⟫ : ℂ) = 0) (h1 : (⟪u1 E Uop v c, z⟫ : ℂ) = 0) :
    (⟪E v, passOp Uop R Ph φ z⟫ : ℂ) = 0 ∧
      (⟪u1 E Uop v c, passOp Uop R Ph φ z⟫ : ℂ) = 0 := by
  have hexp : Complex.exp (-(φ * Complex.I)) * Complex.exp (φ * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hcs : (c : ℂ) * (c : ℂ) + ((sVal c : ℝ) : ℂ) * ((sVal c : ℝ) : ℂ) = 1 := by
    have h2 := sVal_sq hc
    have h3 : sVal c * sVal c = 1 - c * c := by nlinarith [h2]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, h3]
    push_cast
    ring
  have hp0 : passOp Uop R Ph φ (E v)
      = (c : ℂ) • E v - ((sVal c : ℝ) : ℂ) • u1 E Uop v c := pass_emb_n hc h φ
  have hp1 : passOp Uop R Ph φ (u1 E Uop v c)
      = Complex.exp (φ * Complex.I) •
          (((sVal c : ℝ) : ℂ) • E v + (c : ℂ) • u1 E Uop v c) := pass_u1 hc h φ
  -- `E v` and `u₁` in terms of their own pass images
  have hEv : E v = (c : ℂ) • passOp Uop R Ph φ (E v)
      + (Complex.exp (-(φ * Complex.I)) * ((sVal c : ℝ) : ℂ)) •
          passOp Uop R Ph φ (u1 E Uop v c) := by
    rw [hp0, hp1]
    match_scalars
    · linear_combination (-(((sVal c : ℝ) : ℂ) * ((sVal c : ℝ) : ℂ))) * hexp - hcs
    · linear_combination (-((c : ℂ) * ((sVal c : ℝ) : ℂ))) * hexp
  have hU1 : u1 E Uop v c = (-((sVal c : ℝ) : ℂ)) • passOp Uop R Ph φ (E v)
      + (Complex.exp (-(φ * Complex.I)) * (c : ℂ)) •
          passOp Uop R Ph φ (u1 E Uop v c) := by
    rw [hp0, hp1]
    match_scalars
    · linear_combination (-((c : ℂ) * (c : ℂ))) * hexp - hcs
    · linear_combination (-((c : ℂ) * ((sVal c : ℝ) : ℂ))) * hexp
  constructor
  · conv_lhs => rw [hEv]
    rw [inner_add_left, inner_smul_left, inner_smul_left, hpass φ (E v) z,
      hpass φ (u1 E Uop v c) z, h0, h1, mul_zero, mul_zero, add_zero]
  · conv_lhs => rw [hU1]
    rw [inner_add_left, inner_smul_left, inner_smul_left, hpass φ (E v) z,
      hpass φ (u1 E Uop v c) z, h0, h1, mul_zero, mul_zero, add_zero]

/-- The whole walk product preserves the orthocomplement of the walk plane. -/
theorem passProd_orth (h : IsQubitization E Uop R Ph v c) (hc : c ^ 2 < 1)
    (hpass : ∀ φ, IsIsometryOp (passOp Uop R Ph φ)) (φs : ℕ → ℝ) (k n : ℕ)
    {z : H₂} (h0 : (⟪E v, z⟫ : ℂ) = 0) (h1 : (⟪u1 E Uop v c, z⟫ : ℂ) = 0) :
    (⟪E v, passProd Uop R Ph φs k n z⟫ : ℂ) = 0 ∧
      (⟪u1 E Uop v c, passProd Uop R Ph φs k n z⟫ : ℂ) = 0 := by
  induction n generalizing k z with
  | zero =>
      rw [passProd_zero, Module.End.one_apply]
      exact ⟨h0, h1⟩
  | succ n ih =>
      rw [passProd_succ, LinearMap.comp_apply]
      exact ih (k + 1)
        (pass_orth h hc hpass (φs k) h0 h1).1
        (pass_orth h hc hpass (φs k) h0 h1).2

/-! ## §3. The adjoint block value of the whole walk -/

/-- **The adjoint block value of the walk product**: the pulled-back
vacuum-sector vector of the whole phased walk is collinear with the block
vector, `E† (W† (E v)) = conj (P_φ(c)) • v`.  This is what compresses the wp
of the projector `∣E v⟩⟨E v∣` through the walk to `|P_φ(c)|² ∣v⟩⟨v∣` on the
vacuum sector. -/
theorem adjoint_passProd_block (h : IsQubitization E Uop R Ph v c)
    (hc : c ^ 2 < 1) (hpass : ∀ φ, IsIsometryOp (passOp Uop R Ph φ))
    (φs : ℕ → ℝ) (m : ℕ) :
    LinearMap.adjoint E
        (LinearMap.adjoint (passProd Uop R Ph φs 0 m) (E v))
      = (starRingEnd ℂ) (qspPoly c φs m) • v := by
  have hiso : ∀ a b : H₁, (⟪E a, E b⟫ : ℂ) = ⟪a, b⟫ := fun a b => by
    calc (⟪E a, E b⟫ : ℂ)
        = ⟪a, LinearMap.adjoint E (E b)⟫ := (LinearMap.adjoint_inner_right _ _ _).symm
      _ = ⟪a, b⟫ := by rw [h.emb_adj]
  have hvv : (⟪v, v⟫ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), h.norm_v]
    norm_num
  refine ext_inner_left ℂ fun u => ?_
  rw [LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
  have hdecomp : E u = (⟪v, u⟫ : ℂ) • E v + E (u - (⟪v, u⟫ : ℂ) • v) := by
    rw [map_sub, map_smul]
    module
  rw [hdecomp, map_add, map_smul, inner_add_left, inner_smul_left]
  have hWEv : (⟪passProd Uop R Ph φs 0 m (E v), E v⟫ : ℂ)
      = (starRingEnd ℂ) (qspPoly c φs m) := by
    rw [passProd_emb, qsp_product h hc φs m, inner_add_left, inner_smul_left,
      inner_smul_left, inner_emb_self h,
      show (⟪u1 E Uop v c, E v⟫ : ℂ) = 0 from by
        rw [← inner_conj_symm, inner_emb_u1 h, map_zero],
      qspPoly]
    ring
  have horth : (⟪passProd Uop R Ph φs 0 m (E (u - (⟪v, u⟫ : ℂ) • v)), E v⟫ : ℂ)
      = 0 := by
    have hz0 : (⟪E v, E (u - (⟪v, u⟫ : ℂ) • v)⟫ : ℂ) = 0 := by
      rw [hiso, inner_sub_right, inner_smul_right, hvv, mul_one, sub_self]
    have hz1 : (⟪u1 E Uop v c, E (u - (⟪v, u⟫ : ℂ) • v)⟫ : ℂ) = 0 := by
      rw [← inner_conj_symm]
      calc (starRingEnd ℂ) (⟪E (u - (⟪v, u⟫ : ℂ) • v), u1 E Uop v c⟫ : ℂ)
          = (starRingEnd ℂ)
              (⟪u - (⟪v, u⟫ : ℂ) • v, LinearMap.adjoint E (u1 E Uop v c)⟫ : ℂ) := by
            rw [LinearMap.adjoint_inner_right]
        _ = 0 := by rw [emb_adj_u1 h, inner_zero_right, map_zero]
    rw [← inner_conj_symm,
      (passProd_orth h hc hpass φs 0 m hz0 hz1).1, map_zero]
  rw [hWEv, horth, add_zero, inner_smul_right, ← inner_conj_symm v u,
    Complex.conj_conj]
  ring

/-! ## §4. The QSP product at block value `0` and zero angles -/

theorem qspMat_zero_sq : qspMat 0 0 * qspMat 0 0 = -1 := by
  have hs : sVal (0 : ℝ) = 1 := by
    rw [sVal]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qspMat, hs, Matrix.mul_apply, Fin.sum_univ_two]

/-- The QSP product of an even number of zero-angle passes at block value `0`
is `(−1)^m` times the identity. -/
theorem qspProd_zero_even (m : ℕ) :
    qspProd 0 (fun _ => (0 : ℝ)) (2 * m) = ((-1 : ℂ) ^ m) • 1 := by
  induction m with
  | zero => simp [qspProd]
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 from by omega,
        show qspProd (0 : ℝ) (fun _ => (0 : ℝ)) (2 * m + 1 + 1)
          = qspMat 0 0 * (qspMat 0 0 * qspProd 0 (fun _ => (0 : ℝ)) (2 * m)) from rfl,
        ← Matrix.mul_assoc, qspMat_zero_sq, ih]
      rw [Matrix.mul_smul, pow_succ]
      ext i j
      simp [Matrix.smul_apply]
      try ring

/-- The QSP polynomial entry of an even number of zero-angle passes at block
value `0` is the unit `(−1)^m` — a nonzero target amplitude a non-vacuity
witness can hit exactly. -/
theorem qspPoly_zero_even (m : ℕ) :
    qspPoly 0 (fun _ => (0 : ℝ)) (2 * m) = (-1 : ℂ) ^ m := by
  rw [qspPoly, qspProd_zero_even, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one]

end Qhl.Qubitization
