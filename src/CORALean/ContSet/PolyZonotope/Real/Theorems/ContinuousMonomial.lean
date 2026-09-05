import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# A monomial is continuous in the factors

`∏ₖ αₖ^{E[k,i]}` is a polynomial, so it is continuous — the one analytic fact
either polynomial-zonotope representation needs. It is what carries topology
through the dependent block: a constrained polynomial zonotope's coefficient
domain is closed because its constraint rows are continuous in the factors, and
the map onto the set is continuous for the same reason.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {p h : ℕ}

theorem PolyZonotope.continuous_monomial (E : Fin p → Fin h → ℕ) (i : Fin h) :
    Continuous fun a : Fin p → ℝ => PolyZonotope.monomial E a i := by
  simp only [PolyZonotope.monomial]
  exact continuous_finsetProd _ fun k _ => (continuous_apply k).pow (E k i)

end CORALean.Real
