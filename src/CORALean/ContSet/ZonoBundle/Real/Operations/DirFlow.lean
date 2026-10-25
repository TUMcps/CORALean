module

public import CORALean.ContSet.ZonoBundle.Real.Operations.FlowIndex
public import Mathlib.LinearAlgebra.Matrix.RowCol

@[expose] public section

/-!
# `ZonoBundle.dirFlow`: the flow heuristic

The flow method of [1, Heuristic flow]: start from `Λ = I` and replace the column most aligned with
the flow direction `f` by `f` itself. Invertible exactly when that column of `f` is nonzero, i.e.
for any `f ≠ 0`; at `f = 0` the replaced column is zero, which the paper does not consider.

The rule first appeared in [2, Sec. 6.2], with `f` normalized, which changes no
enclosure.

## Inputs
* `f` – flow direction

## Output
* the identity with the most aligned column replaced by the flow

## References

* [1] M. Althoff and B. H. Krogh. "Zonotope Bundles for the Efficient Computation of Reachable
      Sets". 2011 50th IEEE Conference on Decision and Control and European Control Conference
      (CDC-ECC 2011), 2011.
* [2] M. Althoff, O. Stursberg and M. Buss. "Computing Reachable Sets of Hybrid Systems Using a
      Combination of Zonotopes and Polytopes". Nonlinear Analysis: Hybrid Systems, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The flow method [1, Heuristic flow]: `I` with the column `flowIndex f` replaced by `f`. -/
noncomputable def ZonoBundle.dirFlow (f : Vec ℝ n) : Mat ℝ n n :=
  match ZonoBundle.flowIndex f with
  | some i => (1 : Mat ℝ n n).updateCol i f
  | none => 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
