import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff

/-!
# `PolyZonotope.expWeight`

The weight of an edge `i → j` of `[1, Def. 5]`, summed over every factor so that the agreeing
ones contribute nothing: at an edge the columns differ at one index, so it is the single `eDiff`
of the definition. Over a bare exponent matrix, as the edges are.

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and
      Its Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An edge's weight, summed over every factor. -/
def PolyZonotope.expWeight {p h : ℕ} (E : Fin p → Fin h → ℕ) (i j : Fin h) : ℕ :=
  ∑ k, PolyZonotope.eDiff (E k i) (E k j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
