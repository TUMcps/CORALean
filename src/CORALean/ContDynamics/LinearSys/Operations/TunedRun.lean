module

public import CORALean.ContDynamics.LinearSys.Definitions.TunedState
public import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStep
public import CORALean.ContDynamics.LinearSys.Operations.InputSolution
public import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
public import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrder
public import CORALean.ContSet.Zonotope.Real.Operations.Reduce

@[expose] public section

/-!
# `Alg. 1` lines 4-11: the loop

`tunedRun`: [1, Alg. 1] lines 4-11, iterate the tuned step while `t < t_f`. Line 4's `while
t < t_f` is no Lean recursion, so the caller supplies the iteration count and a run that has
reached `t_f` stands still.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
open Matrix ContSet Scalar NormedSpace


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Lines 1-3: the time, the step `Alg. 2` starts from, and the two accumulated
errors, before the first iteration. -/
noncomputable def LinearSys.aux_tunedInit (tf μ : ℝ) : LinearSys.TunedState n :=
  -- 1. t ← 0
  { t := 0
    -- 2. Δt₋₁ ← t_f μ
    Δt := tf * μ
    η := 0
    -- 3. ε_P([0,0]) ← 0
    εP := 0
    -- 3. ε_S([0,0]) ← 0
    εS := 0
    PR := Zonotope.ofPoint 0
    R := Zonotope.ofPoint 0 }

/-- Lines 5-10: one iteration of [1, Alg. 1]'s main loop, and `none` where
`Alg. 2` ran out of fuel. -/
noncomputable def LinearSys.aux_tunedStep (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPmax εSmax tf μ : ℝ) (ηmax fuel : ℕ)
    (s : LinearSys.TunedState n) : Option (LinearSys.TunedState n) :=
  match sys.adaptTimeStep le X₀ U εHmax εPmax s.εP tf s.t s.Δt μ ηmax fuel with
  -- 5. Alg. 2 gave out
  | none => none
  -- 5. Alg. 2
  | some (Δt, η, εP) =>
    -- 6. HR([0,Δt_i])
    let HR₀ := sys.timeIntervalStep (S := 𝒵) Δt η X₀
    -- 6. PR([0,Δt_i])
    let PR₀ := sys.inputSolution (S := 𝒵) Δt η U
    -- 7. eq. (2)'s e^{A t_i}
    let Φti := exp (s.t • toRealMat sys.A)
    -- 7. HR([t_i,t_{i+1}])
    let HR := Zonotope.mtimes Φti HR₀
    -- 7. PR([0,t_{i+1}])
    let PR := Zonotope.plus s.PR (Zonotope.mtimes Φti PR₀)
    -- 8. Alg. 3
    let setOrder := PR.adaptSetOrder le εSmax s.εS tf s.t Δt
    -- 8. red(PR, Φ_set,i)
    let PRred := PR.reduce setOrder.1
    -- 9. R([t_i,t_{i+1}])
    let R := Zonotope.plus HR PRred
    -- 10. t ← t + Δt_i
    some { t := s.t + Δt, Δt := Δt, η := η,
           εP := εP, εS := setOrder.2, PR := PRred, R := R }


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Lines 4-11: iterate the tuned step while `t < t_f`. -/
noncomputable def LinearSys.tunedRun (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPmax εSmax tf μ : ℝ) (ηmax fuel : ℕ) :
    ℕ → Option (LinearSys.TunedState n)
  | 0 => some (LinearSys.aux_tunedInit tf μ)                           -- 1.-3. initialize
  | k + 1 =>
    match sys.tunedRun le X₀ U εHmax εPmax εSmax tf μ ηmax fuel k with
    | none => none
    | some s =>
      if s.t < tf                                                  -- 4. while t < t_f
      then sys.aux_tunedStep le X₀ U εHmax εPmax εSmax tf μ ηmax fuel s
      else some s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
