import CORALean.ContDynamics.LinParamSysDT.Operations.Reach
import CORALean.ContDynamics.LinearSys.Operations.DiscretizeEnclosureFloat
import CORALean.ContDynamics.LinearSys.Operations.InputSolutionFloat
import CORALean.ContDynamics.NeurNetContrSys.Definitions.ReachOptions
import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
import CORALean.ContDynamics.Reach.Definitions.Params
import CORALean.NN.Operations.Enclose

/-!
# A neural-network-controlled continuous plant, reached in floats

`NeurNetContrSys.reach` computed in `𝕋`, at float zonotopes: each control period
encloses the network's output over the period's initial set, takes that as the
plant's input set, and runs `N` steps of the plant sampled by
`discretizeEnclosureFloat` under `inputSolutionFloat` of it — the exact
`discretize` and `inputSolution` replaced by their float enclosures. The order
`η` is the caller's; `reachFloat_outer` asks it to be admissible.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The reachable set at the end of `params.tFinal - params.tStart` control periods,
each `options.N` float steps of `options.timeStep` under one held input set. -/
def NeurNetContrSys.reachFloat (sys : NeurNetContrSys 𝕋 (Zonotope 𝕋) n)
    (params : Reach.Params (Zonotope 𝕋 n) ℕ) (options : NeurNetContrSys.ReachOptions 𝕋) :
    Zonotope 𝕋 n :=
  let R₀ := params.R0                                               -- the paper's symbols
  let Δt := options.timeStep
  let N := options.N
  let η := options.taylorTerms
  let o := options.zonotopeOrder
  let H := params.tFinal - params.tStart                           -- control periods
  let period := fun R =>                                            -- N steps under one held input
    (sys.plant.discretizeEnclosureFloat Δt η).reach
      ⟨R, sys.plant.inputSolutionFloat Δt η (sys.contr.enclose R), 0, N⟩
      ⟨o, options.hZonotopeOrder⟩
  Nat.repeat period H R₀                                            -- R(HNΔt)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
