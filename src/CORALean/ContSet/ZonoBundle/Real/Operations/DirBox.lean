module

public import Mathlib.Data.Matrix.Basic
public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# `ZonoBundle.dirBox`: the box heuristic

The box method of [1, Heuristic box]: `Λ = I`, so the bundle is enclosed by an axis-aligned box and
the dividing hyperplane is normal to a coordinate axis. No computation beyond the identity.

## Inputs
* `n` – dimension

## Output
* the identity direction matrix

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box method [1, Heuristic box]: `Λ = I`. -/
def ZonoBundle.dirBox (n : ℕ) : Mat ℝ n n := 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
