import CORALean.ContSet.PolyZonotope.Real.Operations.OuterApprox
import CORALean.ContSet.PolyZonotope.Real.Theorems.BoxOutOuter

/-!
# `outerApprox` encloses

`outerApprox` is `boxOut` at the generators its scan takes, and `boxOut_outer` holds at every
choice: the result encloses the original for every `tol` and every `id`. An enclosure, not an
equality.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

open scoped Classical in
/-- `outerApprox` encloses the original, whatever `tol` and `id` are. -/
theorem PolyZonotope.outerApprox_outer (pZ : PolyZonotope (Vec ℝ n)) (tol : ℝ)
    (S : Finset (Fin pZ.p)) : pZ.construct ⊆ (pZ.outerApprox tol S).construct :=
  PolyZonotope.boxOut_outer pZ _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
