module

public import CORALean.ContSet.PolyZonotope.Real.Operations.PlusE
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# A left-block generator's monomial under `plusE`

Split out of `Operations/Plus.lean` (issue #62): a proof device rather than an
operation, hence in `Theorems/`, reused across `PlusExact`, `LinCombOuter`,
`DependentExact` and their `ConPolyZono` and float-layer counterparts.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- A generator from the left block sees only the left factors. Stated for an
arbitrary factor vector, since the two inclusions supply it differently: one
appends two vectors, the other restricts one. -/
theorem PolyZonotope.monomial_plusE_left {p₁ h₁ p₂ h₂ : ℕ} (E₁ : Fin p₁ → Fin h₁ → ℕ)
    (E₂ : Fin p₂ → Fin h₂ → ℕ) (a : Fin (p₁ + p₂) → ℝ) (i : Fin h₁) :
    PolyZonotope.monomial (PolyZonotope.plusE E₁ E₂) a (Fin.castAdd h₂ i)
      = PolyZonotope.monomial E₁ (fun k => a (Fin.castAdd p₂ k)) i := by -- --- PROOF ---
  rw [PolyZonotope.monomial, PolyZonotope.monomial, Fin.prod_univ_add]
  have hother : (∏ k : Fin p₂, a (Fin.natAdd p₁ k)
      ^ PolyZonotope.plusE E₁ E₂ (Fin.natAdd p₁ k) (Fin.castAdd h₂ i)) = 1 :=
    Finset.prod_eq_one fun k _ => by
      simp only [PolyZonotope.plusE, Fin.append_right, Fin.append_left, pow_zero]
  have hown : (∏ k : Fin p₁, a (Fin.castAdd p₂ k)
      ^ PolyZonotope.plusE E₁ E₂ (Fin.castAdd p₂ k) (Fin.castAdd h₂ i))
      = ∏ k, a (Fin.castAdd p₂ k) ^ E₁ k i :=
    Finset.prod_congr rfl fun k _ => by
      simp only [PolyZonotope.plusE, Fin.append_left]
  rw [hother, hown, mul_one]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
