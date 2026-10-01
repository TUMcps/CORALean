import Mathlib.Data.Matrix.Basic
import CORALean.Global.Tensor

/-!
# `ZonoBundle.dirBox`: the box heuristic

The box method of [1, Heuristic box]: `Λ = I`, so the bundle is enclosed by an axis-aligned box and
the dividing hyperplane is normal to a coordinate axis. No computation beyond the identity.

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of
      Reachable Sets". In Proc. of the 50th IEEE Conference on Decision and Control and
      European Control Conference (CDC-ECC), pp. 6814-6821, 2011.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box method [1, Heuristic box]: `Λ = I`. -/
def ZonoBundle.dirBox (n : ℕ) : Mat ℝ n n := 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
