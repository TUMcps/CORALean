module

public import CORALean.ContSet.PolyZonotope.Real.Operations.LinCombE
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The centre-difference generator of `linComb` carries only the fresh factor

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

theorem PolyZonotope.monomial_linCombE_last (a : Fin (p₁ + p₂ + 1) → ℝ) :
    PolyZonotope.monomial (PolyZonotope.linCombE E₁ E₂)
        (h := h₁ + h₂ + (h₁ + h₂ + 1)) a
        (Fin.natAdd (h₁ + h₂) (Fin.natAdd (h₁ + h₂) (0 : Fin 1)))
      = a (Fin.natAdd (p₁ + p₂) (0 : Fin 1)) := by -- --- PROOF ---
  rw [PolyZonotope.monomial, Fin.prod_univ_add, Fin.prod_univ_one]
  have hold : (∏ k : Fin (p₁ + p₂), a (Fin.castAdd 1 k)
      ^ PolyZonotope.linCombE E₁ E₂ (Fin.castAdd 1 k)
        (Fin.natAdd (h₁ + h₂) (Fin.natAdd (h₁ + h₂) (0 : Fin 1)))) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [PolyZonotope.linCombE, Fin.append_left, Fin.append_right, pow_zero]
  rw [hold, one_mul]
  simp only [PolyZonotope.linCombE, Fin.append_right, pow_one]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
