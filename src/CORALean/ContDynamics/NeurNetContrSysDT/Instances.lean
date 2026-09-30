import CORALean.ContDynamics.Reach.Reach
import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachUnionOuter

/-!
# `NeurNetContrSysDT` instantiates `Reach`

`params` is `Reach.Params` counted in sampling periods, `options`
`NeurNetContrSysDT.ReachOptions`. `reachExact` is `reachUnionExact` over
`tFinal - tStart` steps, the closed loop being time-invariant, `reach` is
`reachUnion` (always `some`: nothing here can fail at run time), and the guarantee
is `reachUnion_outer`. No input set: the closed loop reads its own input off the
controller.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- ========================================  INSTANCES  ========================================= --

instance NeurNetContrSysDT.reachInstance :
    Reach (NeurNetContrSysDT 𝕋 S) (fun n => Reach.Params (S n) ℕ)
      NeurNetContrSysDT.ReachOptions S where
  reachExact sys params := sys.reachUnionExact (params.tFinal - params.tStart)
    (construct params.R0)
  reach sys params options := some (sys.reachUnion params options)
  reach_outer sys params options := sys.reachUnion_outer params options

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
