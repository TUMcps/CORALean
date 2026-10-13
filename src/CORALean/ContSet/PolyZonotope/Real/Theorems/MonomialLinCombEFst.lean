module

public import CORALean.ContSet.PolyZonotope.Real.Operations.LinCombE
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The first block of `linCombE` keeps the original monomials

Split out of `Operations/LinComb.lean` (issue #62): a proof device rather than
an operation, hence in `Theorems/`, reused by `LinCombOuter.lean` at both
layers.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p₁ h₁ p₂ h₂ : ℕ} (E₁ : Fin p₁ → Fin h₁ → ℕ) (E₂ : Fin p₂ → Fin h₂ → ℕ)


-- =======================================  MAIN THEOREM  ======================================= --

/-- The first block keeps the monomials the two sets brought: the fresh factor
sits there at exponent zero. -/
theorem PolyZonotope.monomial_linCombE_fst (a : Fin (p₁ + p₂ + 1) → ℝ)
    (i : Fin (h₁ + h₂)) :
    PolyZonotope.monomial (PolyZonotope.linCombE E₁ E₂) a (Fin.castAdd (h₁ + h₂ + 1) i)
      = PolyZonotope.monomial (PolyZonotope.plusE E₁ E₂)
          (fun k => a (Fin.castAdd 1 k)) i := by -- --- PROOF ---
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add, Fin.prod_univ_one]
  have hnew : a (Fin.natAdd (p₁ + p₂) (0 : Fin 1))
      ^ PolyZonotope.linCombE E₁ E₂ (Fin.natAdd (p₁ + p₂) (0 : Fin 1))
        (Fin.castAdd (h₁ + h₂ + 1) i) = 1 := by
    simp only [PolyZonotope.linCombE, Fin.append_right, Fin.append_left, pow_zero]
  rw [hnew, mul_one]
  exact Finset.prod_congr rfl fun k _ => by
    simp only [PolyZonotope.linCombE, Fin.append_left]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
