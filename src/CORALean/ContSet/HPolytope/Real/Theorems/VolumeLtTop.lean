import CORALean.ContSet.HPolytope.Real.Operations.Volume
import Mathlib.Topology.MetricSpace.Bounded

/-!
# A bounded polytope has finite volume

The case where CORA's value is a number rather than `Inf`: a bounded set has finite Lebesgue
measure.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.volume_lt_top {P : HPolytope (Vec ℝ n)}
    (h : Bornology.IsBounded P.construct) : P.volume < ⊤ :=
  h.measure_lt_top


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
