import Qhl.Logic.CountedWp

namespace Qhl

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {D : L → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
variable {σT τT : Type*}

private theorem wpSuffixAux_op_congr
    (g : ℕ → Assn σT D → Assn σT D) (h : ℕ → Assn τT D → Assn τT D)
    (Y : Assn σT D) (Z : Assn τT D) (σ : σT) (τ : τT) (n : ℕ)
    (hg : ∀ j, j < n → ∀ A B, A.op σ = B.op τ → (g j A).op σ = (h j B).op τ)
    (hY : Y.op σ = Z.op τ) :
    ∀ m k, m + k ≤ n → (wpSuffixAux g Y m k).op σ = (wpSuffixAux h Z m k).op τ
  | 0, _, _ => hY
  | m + 1, k, hmk =>
      hg k (by omega) _ _ (wpSuffixAux_op_congr g h Y Z σ τ n hg hY m (k + 1) (by omega))

/-- Pointwise equality of suffix effects when each transformer preserves equality. -/
theorem wpSuffix_op_congr
    (g : ℕ → Assn σT D → Assn σT D) (h : ℕ → Assn τT D → Assn τT D)
    (Y : Assn σT D) (Z : Assn τT D) (σ : σT) (τ : τT) (n k : ℕ)
    (hg : ∀ j, j < n → ∀ A B, A.op σ = B.op τ → (g j A).op σ = (h j B).op τ)
    (hY : Y.op σ = Z.op τ) :
    (wpSuffix g n Y k).op σ = (wpSuffix h n Z k).op τ := by
  rcases Nat.lt_or_ge k n with hk | hk
  · exact wpSuffixAux_op_congr g h Y Z σ τ n hg hY (n - k) k (by omega)
  · rw [wpSuffix_of_ge hk, wpSuffix_of_ge hk]
    exact hY

end Qhl
