module

public import CORALean.NN.Theorems.EncloseAtInflate
public import CORALean.NN.Theorems.LinearSigmoidConverges

@[expose] public section

/-!
# The output of `σ(W x + b)` converges to the exact image

[1, Prop. 4.13] itself: on a two-layer network some schedule brings the enclosed output inside any
inflation of the exact image, which with `encloseAt_outer` squeezes the enclosure onto it. Split
from `LinearSigmoidConverges.lean` as `ExistsScheduleSigmoidLinearSigmoidSubset.lean` is from its
own pair. The paper's `h_max → ∞` is not a hypothesis here: `encloseAt` applies no order reduction
at all, so there is no generator budget for a refinement to run into and the limit is taken in the
order pattern alone.

## Inputs
* `W` – weight matrix
* `b` – bias vector
* `X` – input polynomial zonotope
* `ε` – inflation radius

## Hypotheses
* `hε` – radius is positive

## Conclusion
* some schedule encloses the output inside the exact image inflated by the radius

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Pointwise ContSet

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem exists_schedule_linearSigmoid_subset (W : Mat ℝ m n) (b : Vec ℝ m)
    (X : Real.PolyZonotope (Vec ℝ n)) {ε : ℝ} (hε : 0 < ε) : ∃ sch : Schedule,
      construct ((Real.linearSigmoidNetwork W b).encloseAt sch X)
        ⊆ (Real.linearSigmoidNetwork W b).image (construct X) + Metric.closedBall 0 ε :=
  (Real.linearSigmoidNetwork W b).exists_schedule_encloseAt_subset
    (linearSigmoidNetwork_isConvergent W b) X ε hε

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
