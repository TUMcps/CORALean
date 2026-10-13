module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.monomial_add`

Exponent columns add where monomials multiply — what keeps the representation
closed under a quadratic map, which sums exponent columns pairwise.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Exponent columns add where monomials multiply, which is what keeps the
representation closed under a quadratic map. -/
theorem PolyZonotope.monomial_add {p h : ℕ} (E₁ E₂ : Fin p → Fin h → ℕ) (a : Fin p → ℝ)
    (i : Fin h) :
    PolyZonotope.monomial (fun k i => E₁ k i + E₂ k i) a i
      = PolyZonotope.monomial E₁ a i * PolyZonotope.monomial E₂ a i := by
  rw [PolyZonotope.monomial, PolyZonotope.monomial, PolyZonotope.monomial,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => pow_add (a k) (E₁ k i) (E₂ k i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
