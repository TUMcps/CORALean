module

public import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
public import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachFloat

@[expose] public section

/-!
# The reachable sets at every control-period boundary, in floats

`NeurNetContrSys.reachUnion` computed in `𝕋`: the periods `0` through
`tFinal - tStart` of `reachFloat`, from `R0`, at `η` raised by
`LinearSys.reachOrderFloat` to an order admissible for the step `Δt` at the augmented matrix
`[A B; 0 0]` (`augmentFloat`). `none` when no such order is found.
-/

-- Authors:       Claude Sonnet 5.5, Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sets `R(iNΔt)`, `i ≤ tFinal - tStart`, one per control-period boundary. -/
def NeurNetContrSys.reachUnionFloat (sys : NeurNetContrSys (LinearSys 𝕋 n) 𝒵[𝕋] n)
    (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℕ) (options : NeurNetContrSys.ReachOptions 𝕋) :
    Option (List (Zonotope (Vec 𝕋 n))) := do
  let R₀ := params.X₀                                               -- the paper's symbols
  let Δt := options.Δt
  let H := params.tFinal - params.tStart                           -- control periods
  let η ← sys.augmentFloat.reachOrderFloat Δt Δt options.η      -- raised until admissible
  pure ((List.range (H + 1)).map (fun i =>                          -- R(iNΔt), every i ≤ H
    sys.reachFloat ⟨R₀, 0, i⟩
      ⟨Δt, options.N, η, options.ρ, options.hZonotopeOrder⟩))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
