module

public import CORALean.ContSet.Taylm.Float.Operations.MonomialRange
public import CORALean.ContSet.Taylm.Real.Theorems.AbsMonomialLeOne

@[expose] public section

/-!
# `Taylm.monomialRange` holds the monomial

## Inputs
* `t` – point of the box
* `e` – exponents of the monomial

## Hypotheses
* `ht` – `t` lies in the box `[-1, 1]ⁿ`

## Conclusion
* the monomial at `t` lies in its range
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.monomialRange_mem {t : Vec ℝ n} (ht : t ∈ Real.Taylm.box n)
    (e : Fin n → ℕ) : -- --- CONCL ---
    toReal (Taylm.monomialRange (𝕋 := 𝕋) e).inf ≤ Real.Taylm.monomial e t ∧
      Real.Taylm.monomial e t ≤ toReal (Taylm.monomialRange (𝕋 := 𝕋) e).sup := by -- --- PROOF ---
  have hm := abs_le.1 (Real.Taylm.abs_monomial_le_one ht e)
  unfold Taylm.monomialRange
  split_ifs with h₀ h₁
  · -- the constant monomial: every exponent is zero
    have he : ∀ k, e k = 0 := fun k =>
      (Finset.sum_eq_zero_iff.1 h₀) k (Finset.mem_univ k)
    simp [Real.Taylm.monomial, he, toReal_one]
  · simp only [toReal_neg, toReal_one]
    exact hm
  · -- every exponent even: a product of even powers
    push Not at h₁
    have hev : ∀ k, Even (e k) := fun k => Nat.even_iff.2 (by have := h₁ k; omega)
    refine ⟨?_, by rw [toReal_one]; exact hm.2⟩
    rw [toReal_zero]
    exact Finset.prod_nonneg fun k _ => (hev k).pow_nonneg (t k)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
