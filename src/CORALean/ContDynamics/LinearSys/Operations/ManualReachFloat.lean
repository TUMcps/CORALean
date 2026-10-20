module

public import CORALean.ContDynamics.LinearSys.Definitions.ManualStateFloat
public import CORALean.ContDynamics.LinearSys.Definitions.ReachOptions
public import CORALean.ContDynamics.LinearSys.Operations.InputSetFloat
public import CORALean.ContDynamics.LinearSys.Operations.ManualRunFloat
public import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
public import CORALean.ContDynamics.Reach.Definitions.InputParams
public import CORALean.ContDynamics.Reach.Operations.Steps
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.Global.Float.ToRat

@[expose] public section

/-!
# `Alg. 1` in floats: reachability at a fixed step, order and zonotope order

`ẋ = Ax + Bu + c`, `u(t) ∈ U` arbitrary in time, from `X₀` over `[tStart, tFinal]`, by
[1, Alg. 1] computed in `𝕋`: `N = (tFinal - tStart)/Δt` iterations from `aux_manualInitFloat`,
returning `R̂(τ_0), …, R̂(τ_{N-1})`. `B` and `c` are the system's; `V = B U ⊕ c`
(`inputSetFloat`) is split at its stored center, so `0 ∈ U` is not asked. The order `η` is
raised until the float enclosures admit it (`reachOrderFloat`), as the other float reaches
raise it; `Δt` must divide the horizon exactly.

## Inputs
* `sys` – linear system
* `params` – reach parameters with initial and input sets
* `options` – reach options

## Output
* float windows of the run, if it completes

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of
      Linear Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE
      Transactions on Automatic Control, vol. 68, no. 12, 2023, pp. 7771–7786.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}
open CORALean.Float FloatOps


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Lines 1-2, before the first iteration. -/
def LinearSys.aux_manualInitFloat (X₀ : Zonotope (Vec 𝕋 n)) : LinearSys.ManualStateFloat 𝕋 n :=
  { t := 0, tLo := zero, tHi := zero                                -- 1. t₀ ← 0
    H := X₀                                                         -- 2. H(t₀) ← X₀
    Pu := Interval.point fun _ => zero                              -- 2. P^u(t₀) ← 0
    PU := (Interval.point fun _ => zero).zonotope }                 -- 2. P̂^U(t₀) ← 0


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the windows `R̂(τ_0), …, R̂(τ_{N-1})` of `ẋ = Ax + Bu + c` from `X₀` under
inputs in `U`, or `none`. -/
def LinearSys.manualReachFloat (sys : LinearSys 𝕋 n)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 sys.m)) ℚ)
    (options : LinearSys.ReachOptions 𝕋) : Option (List (Zonotope (Vec 𝕋 n))) := do
  let X₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let η := options.η
  let ρ := options.ρ
  let N ← Reach.steps params.tStart params.tFinal (ToRat.toRat Δt) -- (tFinal - tStart) / Δt ∈ ℕ
  let η' ← sys.reachOrderFloat Δt Δt η                              -- η, raised until admissible
  let V := sys.inputSetFloat params.U                               -- B U ⊕ c, in the state space
  -- 1.-11. the loop over the time steps, from the initial state
  sys.manualRunFloat X₀ V Δt η' ρ N (LinearSys.aux_manualInitFloat X₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
