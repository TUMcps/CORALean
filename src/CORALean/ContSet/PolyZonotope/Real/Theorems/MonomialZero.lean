import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# `PolyZonotope.monomial_zero`

Every factor at exponent zero collapses the monomial to `1`: the shape a
concatenation gives the generators it did not come from.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

/-- Every factor at exponent zero, so the monomial is `1`: the shape a
concatenation gives the generators it did not come from. -/
theorem PolyZonotope.monomial_zero {p h : ℕ} {E : Fin p → Fin h → ℕ} (a : Fin p → ℝ)
    {i : Fin h} (hE : ∀ k, E k i = 0) : PolyZonotope.monomial E a i = 1 := by
  rw [PolyZonotope.monomial]
  exact Finset.prod_eq_one fun k _ => by rw [hE k, pow_zero]

end CORALean.Real
