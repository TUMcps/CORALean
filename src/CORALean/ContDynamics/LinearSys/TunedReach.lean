import CORALean.ContDynamics.LinearSys.Operations.AdaptTimeStep
import CORALean.ContDynamics.LinearSys.Operations.InputSolution
import CORALean.ContDynamics.LinearSys.Operations.TimeIntervalStep
import CORALean.ContSet.Zonotope.Real.Operations.ReduceBoxError
import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrderLoop
import CORALean.ContSet.Zonotope.Real.Operations.AdaptSetOrder
import CORALean.ContSet.Zonotope.Real.Instances
import CORALean.ContSet.Zonotope.Real.Operations.Reduce

/-!
# `Alg. 1`: fully automated parameter tuning

[1, Alg. 1]: `Alg. 2` picks `Δt_i` and `Φ_prop,i`, eq. (2) carries the two
solutions to the `i`-th interval, `Alg. 3` picks `Φ_set,i` and reduces
`PR([0,t_{i+1}])`, and their sum is `R([t_i,t_{i+1}])`. One iteration is
`tunedStep`, the loop of lines 4-11 is `tunedRun`, and line 12's union is
`tunedReach`.

Three departures, all forced. `Alg. 2` may give out, so a run is an `Option`.
Line 4's `while t < t_f` is no Lean recursion, so the caller supplies the
iteration count and a run that has reached `t_f` stands still. And line 12
unions the steps' sets, which is no zonotope, so `tunedReach` is a `Set`.

Nothing here clips `Δt_i` to what is left of the horizon — [1] does not either
— so a run can step past `t_f`; the accompanying theorem asks that it does not.

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

/-- What one iteration of [1, Alg. 1] hands the next. -/
structure LinearSys.TunedState (n : ℕ) where
  /-- `t_i`, line 10. -/
  t : ℝ
  /-- `Δt_{i-1}`, the step `Alg. 2` enlarges at its own line 1. -/
  Δt : ℝ
  /-- `Φ_prop,i`, the truncation order `Alg. 2` settled on. -/
  η : ℕ
  /-- `ε_P([0,t_i])`, eq. (9). -/
  εP : ℝ
  /-- `ε_S([0,t_i])`, eq. (12). -/
  εS : ℝ
  /-- `PR([0,t_i])`, eq. (2), as `Alg. 3` last reduced it. -/
  PR : Zonotope (Vec ℝ n)
  /-- `R([t_{i-1},t_i])`, line 9. -/
  R : Zonotope (Vec ℝ n)

/-- Lines 1-3: the time, the step `Alg. 2` starts from, and the two accumulated
errors, before the first iteration. -/
noncomputable def LinearSys.tunedInit (tf μ : ℝ) : LinearSys.TunedState n :=
  { t := 0                                                       -- 1. t ← 0
    Δt := tf * μ                                                  -- 2. Δt₋₁ ← t_f μ
    η := 0
    εP := 0                                                       -- 3. ε_P([0,0]) ← 0
    εS := 0                                                       -- 3. ε_S([0,0]) ← 0
    PR := Zonotope.ofPoint 0
    R := Zonotope.ofPoint 0 }

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

/-- Lines 4-11: iterate the tuned step while `t < t_f`. -/
noncomputable def LinearSys.tunedRun (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPmax εSmax tf μ : ℝ) (ηmax fuel : ℕ) :
    ℕ → Option (LinearSys.TunedState n)
  | 0 => some (LinearSys.tunedInit tf μ)                           -- 1.-3. initialize
  | k + 1 =>
    match sys.tunedRun le X₀ U εHmax εPmax εSmax tf μ ηmax fuel k with
    | none => none
    | some s =>
      if s.t < tf                                                  -- 4. while t < t_f
      then sys.tunedStep le X₀ U εHmax εPmax εSmax tf μ ηmax fuel s
      else some s


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1] line 12: `R([0,t_f])`, the union of the first `K` iterations'
time-interval sets. -/
noncomputable def LinearSys.tunedReach (sys : LinearSys 𝕋 n) (le : ℝ → ℝ → Bool)
    (X₀ U : Zonotope (Vec ℝ n)) (εHmax εPmax εSmax tf μ : ℝ) (ηmax fuel K : ℕ) :
    Set (Vec ℝ n) :=
  ⋃ i < K, ⋃ s ∈ sys.tunedRun le X₀ U εHmax εPmax εSmax tf μ ηmax fuel (i + 1), construct s.R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
