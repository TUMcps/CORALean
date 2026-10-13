import CORALean.ContSet.PolyZonotope.Real.PolyZonotope
import Mathlib.Topology.Algebra.Ring.Real

/-!
# A monomial is continuous in the factors

`∏ₖ αₖ^{E[k,i]}` is a polynomial, so it is continuous — the one analytic fact
either polynomial-zonotope representation needs. It is what carries topology
through the dependent block: a constrained polynomial zonotope's coefficient
domain is closed because its constraint rows are continuous in the factors, and
the map onto the set is continuous for the same reason.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {p h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.continuous_monomial (E : Fin p → Fin h → ℕ) (i : Fin h) :
    Continuous fun a : Fin p → ℝ => PolyZonotope.monomial E a i := by
  simp only [PolyZonotope.monomial]
  exact continuous_finsetProd _ fun k _ => (continuous_apply k).pow (E k i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
