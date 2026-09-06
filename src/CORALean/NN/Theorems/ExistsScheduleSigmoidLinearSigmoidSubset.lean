import CORALean.NN.Theorems.MultiLayerRefinementConverges

/-!
# The loop converges on a genuine three-layer chain

Split out of `MultiLayerRefinementConverges.lean` (issue #62): both
declarations there were genuinely public and neither used the other outside
the file, so demoting one to `aux_` would have left the file with none —
split instead, one file each, as `SigmoidRefinementConverges.lean`'s pair
does too.

Some schedule is inside any inflation of the exact output set, which with
`propagateAt_outer` squeezes the enclosure onto it.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_schedule_sigmoidLinearSigmoid_subset (W : Mat ℝ m n) (b : Vec ℝ m)
    (X : PolyZonotope (Vec ℝ n)) {ε : ℝ} (hε : 0 < ε) : ∃ sch : Schedule,
      construct ((sigmoidLinearSigmoidNetwork W b).propagateAt sch X)
        ⊆ (sigmoidLinearSigmoidNetwork W b).outputSet X + Metric.closedBall 0 ε :=
  (sigmoidLinearSigmoidNetwork W b).exists_schedule_propagateAt_subset
    (sigmoidLinearSigmoidNetwork_convergent W b) X ε hε

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
