import CORALean.NN.Theorems.SigmoidRefinementConverges

/-!
# The loop converges at a single sigmoid layer

Split out of `SigmoidRefinementConverges.lean` (issue #62): both declarations
there were genuinely public and neither used the other outside the file, so
demoting one to `aux_` would have left the file with none — split instead,
one file each, as `MultiLayerRefinementConverges.lean`'s pair does too.

Some schedule is inside any inflation of the exact image, which with
`encloseAt_outer` squeezes the enclosure onto it.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise ContSet


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_schedule_sigmoid_subset {n : ℕ} (X : Real.PolyZonotope (Vec ℝ n)) {ε : ℝ}
    (hε : 0 < ε) : ∃ sch : Schedule,
      construct ((Real.sigmoidRefinableNetwork n).encloseAt sch X)
        ⊆ (Real.sigmoidRefinableNetwork n).image (construct X) + Metric.closedBall 0 ε :=
  (Real.sigmoidRefinableNetwork n).exists_schedule_encloseAt_subset
    (sigmoidRefinableNetwork_convergent n) X ε hε

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
