module

public import CORALean.ContDynamics.LinearSys.Operations.AdaptiveRunFloat
public import CORALean.ContDynamics.Reach.Definitions.InputParams

@[expose] public section

/-!
# Adaptive reachability in floats: [1, Alg. 1], CORA's `priv_reach_adaptive`

`ẋ = Ax + Bu`, `u(t) ∈ U` arbitrary in time, from `X₀` over `[tStart, tFinal]`,
in `𝕋`, every step size, truncation order and reduction order chosen against
[1]'s three error budgets. `V = B U` is split at its stored centre, so `0 ∈ U`
is not asked. The time is shifted to start at `0`, as CORA shifts it, and
`Δt_{-1} = t_f μ` (line 2) makes the first step try the whole horizon.

The tuning decides how tight the windows are and how many there are; it
never decides whether they are sound, which every step's float enclosures
settle on their own.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Alg. 1]: the steps covering `[tStart, tFinal]`, each with its window
`R([t_i,t_{i+1}])` and the parameters it was tuned to, or `none`. -/
def LinearSys.reachAdaptiveFloat (sys : LinearSys 𝕋 n) (B : Mat 𝕋 n m)
    (params : Reach.InputParams (Zonotope (Vec 𝕋 n)) (Zonotope (Vec 𝕋 m)) ℚ)
    (options : LinearSys.AdaptiveOptions 𝕋) :
    Option (List (LinearSys.AdaptiveStepInfo 𝕋 n)) :=
  let X₀ := params.X₀                                               -- the paper's symbols
  let V := Mtimes.mtimes (𝕄 := Mat 𝕋)  -- B U, in the state space
    (S := fun k => Zonotope (Vec 𝕋 k)) B params.U
  let tf := params.tFinal - params.tStart                           -- shifted to start at 0
  let s₀ : LinearSys.AdaptiveState 𝕋 n :=                           -- 1.-3. initialize
    { t := 0, tLo := zero, tHi := zero,                             -- 1. t ← 0
      Δt := mulDown (ratUp tf) options.μ,                           -- 2. Δt₋₁ ← t_f μ
      εP := 0, εS := 0,                                             -- 3. ε_P ← 0, ε_S ← 0
      P := (Interval.point fun _ => zero).zonotope }                -- nothing contributed yet
  if 0 < tf then sys.adaptiveRunFloat X₀ V params.tStart tf options options.maxSteps s₀
  else none

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
