module

public import CORALean.NN.Definitions.RefinableLayer
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

@[expose] public section

/-!
# What it takes for one layer's refinement to converge

Stated by a Minkowski inflation and no metric on sets: some order pattern
brings the enclosure inside the exact image widened by any closed `ε`-ball.
`Pointwise` addition does all the work, with no Hausdorff distance to define,
to relate to `construct`, or to prove complete.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise ContSet

variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Some pattern brings the enclosure inside any inflation of the exact image. -/
def RefinableLayer.Convergent (L : RefinableLayer S n m) : Prop :=
  ∀ (s : S n) (ε : ℝ), 0 < ε →
    ∃ t : OrderPattern n,
      construct (L.enclose t s) ⊆ L.eval '' construct s + Metric.closedBall 0 ε

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
