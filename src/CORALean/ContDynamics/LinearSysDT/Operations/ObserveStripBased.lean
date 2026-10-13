import CORALean.ContDynamics.LinearSysDT.Operations.ObserveStep
import CORALean.ContSet.Zonotope.Real.Operations.Reduce

/-!
# The strip-based observer

CORA's `observe_stripBased`, the loop of [1, Alg. 1]: the initial set `R₀` met with the first
measurement's strips, then at every step the prediction and update of `observeStep` followed
by `reduce` to `ρ` ([1, Prop. 3] is one such reduction). The strip widths are
CORA's `sigma = supremum(abs(interval(params.V)))`, here `σ`, so a noise `v ∈ V` needs only
`|vᵢ| ≤ σᵢ`. CORA's estimators `FRad-A`, `FRad-B`, `PRad-A` to `PRad-D` and `VolMin-A` are
this loop at their own gains; `observeStripBased_outer` holds for every gain.

[2, Eq. 4], over time.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] M. Althoff. "Guaranteed State Estimation in CORA 2021". In Proc. of the 8th
      International Workshop on Applied Verification of Continuous and Hybrid Systems (ARCH21),
      EPiC Series in Computing, vol. 80, pp. 161-175, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `R k`, the set the observer holds after the measurement `y k`. -/
noncomputable def LinearSysDT.observeStripBased (sys : LinearSysDT ℝ n) (C : Mat ℝ p n)
    (σ : Vec ℝ p) (W R₀ : Zonotope (Vec ℝ n)) (u : ℕ → Vec ℝ n) (y : ℕ → Vec ℝ p)
    (options : LinearSysDT.ObserveStripOptions n p) : ℕ → Zonotope (Vec ℝ n)
  | 0 =>
    if options.sequential then R₀.intersectStripSeq C σ (y 0) options.gain
    else R₀.intersectStrip C σ (y 0) (options.gain R₀)
  | k + 1 =>
    (sys.observeStep C σ W options (u k) (y (k + 1))
      (sys.observeStripBased C σ W R₀ u y options k)).reduce options.ρ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
