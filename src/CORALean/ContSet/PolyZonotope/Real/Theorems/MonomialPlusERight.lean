module

public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# A right-block generator's monomial under `plusE`

Split out of `Operations/Plus.lean` (issue #62): the mirror of
`MonomialPlusELeft.lean`, where the other set's factors contribute `1`, reused
alongside it wherever `plusE` is unfolded.

## Inputs
* `p₁` – first factor count
* `h₁` – first generator count
* `p₂` – second factor count
* `h₂` – second generator count
* `E₁` – first exponent matrix
* `E₂` – second exponent matrix
* `a` – factor values
* `i` – generator index of the second block

## Hypotheses
* none

## Conclusion
* the monomial reads only the second set's factors
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.monomial_plusE_right {p₁ h₁ p₂ h₂ : ℕ} (E₁ : Fin p₁ → Fin h₁ → ℕ)
    (E₂ : Fin p₂ → Fin h₂ → ℕ) (a : Fin (p₁ + p₂) → ℝ) (i : Fin h₂) : -- --- CONCL ---
    PolyZonotope.monomial (PolyZonotope.plusE E₁ E₂) a (Fin.natAdd h₁ i)
      = PolyZonotope.monomial E₂ (fun k => a (Fin.natAdd p₁ k)) i := by -- --- PROOF ---
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add]
  have hother : (∏ k : Fin p₁, a (Fin.castAdd p₂ k)
      ^ PolyZonotope.plusE E₁ E₂ (Fin.castAdd p₂ k) (Fin.natAdd h₁ i)) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [PolyZonotope.plusE, Fin.append_left, Fin.append_right, pow_zero]
  have hown : (∏ k : Fin p₂, a (Fin.natAdd p₁ k)
      ^ PolyZonotope.plusE E₁ E₂ (Fin.natAdd p₁ k) (Fin.natAdd h₁ i))
      = ∏ k, a (Fin.natAdd p₁ k) ^ E₂ k i :=
    Finset.prod_congr rfl fun k _ => by
      simp only [PolyZonotope.plusE, Fin.append_right]
  rw [hother, hown, one_mul]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
