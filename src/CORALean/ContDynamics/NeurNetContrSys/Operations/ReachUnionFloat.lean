import CORALean.ContDynamics.LinearSys.Operations.ReachOrderFloat
import CORALean.ContDynamics.NeurNetContrSys.Operations.ReachFloat

/-!
# The reachable sets at every control-period boundary, in floats

`NeurNetContrSys.reachUnion` computed in `𝕋`: the periods `0` through
`tFinal - tStart` of `reachFloat`, from `R0`, at `taylorTerms` raised by
`LinearSys.reachOrderFloat` to an order admissible for the step `timeStep` at
`sys.plant.A`. `none` when no such order is found.
-/

-- Authors:       Tobias Ladner
-- Written:       08-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sets `R(iNΔt)`, `i ≤ tFinal - tStart`, one per control-period boundary. -/
def NeurNetContrSys.reachUnionFloat (sys : NeurNetContrSys 𝕋 (fun k => Zonotope (Vec 𝕋 k)) n)
    (params : Reach.Params (Zonotope (Vec 𝕋 n)) ℕ) (options : NeurNetContrSys.ReachOptions 𝕋) :
    Option (List (Zonotope (Vec 𝕋 n))) := do
  let R₀ := params.R0                                               -- the paper's symbols
  let Δt := options.timeStep
  let H := params.tFinal - params.tStart                           -- control periods
  let η ← sys.plant.reachOrderFloat Δt Δt options.taylorTerms      -- raised until admissible
  pure ((List.range (H + 1)).map (fun i =>                          -- R(iNΔt), every i ≤ H
    sys.reachFloat ⟨R₀, 0, i⟩
      ⟨Δt, options.N, η, options.zonotopeOrder, options.hZonotopeOrder⟩))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
