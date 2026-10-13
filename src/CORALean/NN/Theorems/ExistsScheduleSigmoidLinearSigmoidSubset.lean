module

public import CORALean.NN.Theorems.MultiLayerRefinementConverges

@[expose] public section

/-!
# The loop converges on a genuine three-layer chain

Split out of `MultiLayerRefinementConverges.lean` (issue #62): both
declarations there were genuinely public and neither used the other outside
the file, so demoting one to `aux_` would have left the file with none —
split instead, one file each, as `SigmoidRefinementConverges.lean`'s pair
does too.

Some schedule is inside any inflation of the exact image, which with
`encloseAt_outer` squeezes the enclosure onto it.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_schedule_sigmoidLinearSigmoid_subset (W : Mat ℝ m n) (b : Vec ℝ m)
    (X : Real.PolyZonotope (Vec ℝ n)) {ε : ℝ} (hε : 0 < ε) : ∃ sch : Schedule,
      construct ((Real.sigmoidLinearSigmoidNetwork W b).encloseAt sch X)
        ⊆ (Real.sigmoidLinearSigmoidNetwork W b).image (construct X) + Metric.closedBall 0 ε :=
  (Real.sigmoidLinearSigmoidNetwork W b).exists_schedule_encloseAt_subset
    (sigmoidLinearSigmoidNetwork_convergent W b) X ε hε

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
