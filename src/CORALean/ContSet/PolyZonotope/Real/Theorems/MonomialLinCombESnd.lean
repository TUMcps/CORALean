module

public import CORALean.ContSet.PolyZonotope.Real.Operations.LinCombE
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The second block of `linCombE` is the first times the fresh factor

Split out of `Operations/LinComb.lean` (issue #62): a proof device rather than
an operation, hence in `Theorems/`, reused by `LinCombOuter.lean` at both
layers — the whole of what makes `linComb` exact on the dependent part.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p₁ h₁ p₂ h₂ : ℕ} (E₁ : Fin p₁ → Fin h₁ → ℕ) (E₂ : Fin p₂ → Fin h₂ → ℕ)


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.monomial_linCombE_snd (a : Fin (p₁ + p₂ + 1) → ℝ)
    (i : Fin (h₁ + h₂)) :
    PolyZonotope.monomial (PolyZonotope.linCombE E₁ E₂) a
        (Fin.natAdd (h₁ + h₂) (Fin.castAdd 1 i))
      = a (Fin.natAdd (p₁ + p₂) (0 : Fin 1))
          * PolyZonotope.monomial (PolyZonotope.plusE E₁ E₂)
              (fun k => a (Fin.castAdd 1 k)) i := by -- --- PROOF ---
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add, Fin.prod_univ_one]
  have hnew : a (Fin.natAdd (p₁ + p₂) (0 : Fin 1))
      ^ PolyZonotope.linCombE E₁ E₂ (Fin.natAdd (p₁ + p₂) (0 : Fin 1))
        (Fin.natAdd (h₁ + h₂) (Fin.castAdd 1 i))
      = a (Fin.natAdd (p₁ + p₂) (0 : Fin 1)) := by
    simp only [PolyZonotope.linCombE, Fin.append_right, pow_one]
  rw [hnew, mul_comm]
  refine congrArg _ (Finset.prod_congr rfl fun k _ => ?_)
  simp only [PolyZonotope.linCombE, Fin.append_left, Fin.append_right]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
