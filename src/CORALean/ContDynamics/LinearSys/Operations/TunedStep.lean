import CORALean.ContDynamics.LinearSys.Definitions.TunedState
import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStep
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrder
import CORALean.ContSet.Zonotope.Real.Operations.Reduce

/-!
# `Alg. 1` lines 5-10: one iteration of the main loop

`tunedStep`: [1, Alg. 1]. `Alg. 2` picks `Δt_i` and `Φ_prop,i`, eq. (2) carries the two
solutions to the `i`-th interval, `Alg. 3` picks `Φ_set,i` and reduces `PR([0,t_{i+1}])`,
and their sum is `R([t_i,t_{i+1}])`. `none` where `Alg. 2` ran out of fuel.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 5-10: one iteration of [1, Alg. 1]'s main loop, and `none` where
`Alg. 2` ran out of fuel. -/
noncomputable def LinearSys.tunedStep (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPmax εSmax tf μ : ℝ) (ηmax fuel : ℕ)
    (s : LinearSys.TunedState n) : Option (LinearSys.TunedState n) :=
  match sys.adaptTimeStep le X₀ U εHmax εPmax s.εP tf s.t s.Δt μ ηmax fuel with
  | none => none                                                  -- 5. Alg. 2 gave out
  | some (Δt, η, εP) =>                                           -- 5. Alg. 2
    let HR₀ := sys.timeIntervalStep (S := 𝒵) Δt η X₀               -- 6. HR([0,Δt_i])
    let PR₀ := sys.inputSolution (S := 𝒵) Δt η U                   -- 6. PR([0,Δt_i])
    let Φti := exp (s.t • toRealMat sys.A)                         -- 7. eq. (2)'s e^{A t_i}
    let HR := Zonotope.mtimes Φti HR₀                              -- 7. HR([t_i,t_{i+1}])
    let PR := Zonotope.plus s.PR (Zonotope.mtimes Φti PR₀)         -- 7. PR([0,t_{i+1}])
    let setOrder := PR.adaptSetOrder le εSmax s.εS tf s.t Δt       -- 8. Alg. 3
    let PRred := PR.reduce setOrder.1                              -- 8. red(PR, Φ_set,i)
    let R := Zonotope.plus HR PRred                                -- 9. R([t_i,t_{i+1}])
    some { t := s.t + Δt, Δt := Δt, η := η,                        -- 10. t ← t + Δt_i
           εP := εP, εS := setOrder.2, PR := PRred, R := R }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
