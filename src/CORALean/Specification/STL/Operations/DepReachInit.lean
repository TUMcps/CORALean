import CORALean.ContSet.Zonotope.Real.Operations.MtimesIntervalMat
import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
import CORALean.ContSet.Zonotope.Real.Operations.Plus
import CORALean.Specification.STL.Definitions.DepReachConsts
import CORALean.Specification.STL.Definitions.DepReachState
import CORALean.Specification.STL.Operations.DepBox

/-!
# Lines 2-3 of the dependency preserving reachability algorithm

[1, Alg. 1], line 2: `H(t₀), R(t₀) ← X₀`, `P(t₀), P_c(t₀), D₀ ← 0`, and line 3:
`C₀ ← interval(F X₀ ⊕ G ũ)`, with `F X₀` and `G ũ` the interval matrices applied by
`Zonotope.mtimesIntervalMat`. `P(t₀) = P_c(t₀) ⊕ D₀` is the origin as well.

## References

* [1] N. Kochdumper and S. Bak. "Fully Automated Verification of Linear Time-Invariant Systems
      against Signal Temporal Logic Specifications via Reachability Analysis". Nonlinear Analysis:
      Hybrid Systems, vol. 53, 2024, 101491.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 2-3 of [1, Alg. 1]: the state at `t₀ = 0`. -/
noncomputable def STL.depReachInit (X₀ : Zonotope (Vec ℝ n)) (cs : STL.DepReachConsts n) :
    STL.DepReachState n :=
  let H₀ := X₀                                                       -- H(t₀) ← X₀
  let Pc₀ : Zonotope (Vec ℝ n) := Zonotope.ofPoint 0                 -- P_c(t₀) ← 0
  let D₀ : Zonotope (Vec ℝ n) := Zonotope.ofPoint 0                  -- D₀ ← 0
  let C₀ := STL.depBox ((Zonotope.mtimesIntervalMat cs.F X₀).plus
    (Zonotope.mtimesIntervalMat cs.G (Zonotope.ofPoint cs.ũ)))       -- C₀ ← interval(F X₀ ⊕ G ũ)
  ⟨H₀, Pc₀, D₀, C₀⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
