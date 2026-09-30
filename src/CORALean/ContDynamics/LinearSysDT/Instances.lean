import CORALean.ContDynamics.Reach.Reach
import CORALean.ContDynamics.LinearSysDT.Theorems.ReachUnionOuter

/-!
# `LinearSysDT` instantiates `Reach`

`params` is `Reach.InputParams` counted in sampling periods, `U` among them as in
CORA; `options` is `LinearSysDT.ReachOptions`. `reachExact` is `reachUnionExact`
over `tFinal - tStart` steps, the system being time-invariant, `reach` is
`reachUnion` (always `some`: nothing here can fail at run time), and the guarantee
is `reachUnion_outer` — nothing new, every field already proved for its own
sake in `Definitions`, `Operations` and `Theorems`.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- ========================================  INSTANCES  ========================================= --

instance LinearSysDT.reachInstance :
    Reach (LinearSysDT 𝕋) (fun n => Reach.InputParams (S n) (S n) ℕ)
      LinearSysDT.ReachOptions S where
  reachExact sys params := sys.reachUnionExact params.R0 params.U (params.tFinal - params.tStart)
  reach sys params options := some (sys.reachUnion params options)
  reach_outer sys params options := sys.reachUnion_outer params options

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
