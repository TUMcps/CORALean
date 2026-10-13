import CORALean.ContSet.Fullspace.Real.Fullspace
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Full space is full-dimensional

Its interior is itself, which is nonempty in every dimension. Stated at `construct`, which is what
`ContSet.IsFullDim` unfolds to: the `ContSet` instance is declared after the theorems.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Fullspace.isFullDim (F : Fullspace n) :
    (interior F.construct).Nonempty := by
  change (interior (Set.univ : Set (Vec ℝ n))).Nonempty
  rw [interior_univ]
  exact Set.univ_nonempty

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
