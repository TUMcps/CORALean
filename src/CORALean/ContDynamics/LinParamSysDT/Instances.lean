module

public import CORALean.ContDynamics.Reach.Reach
public import CORALean.ContDynamics.LinParamSysDT.Theorems.ReachUnionOuter

@[expose] public section

/-!
# `LinParamSysDT` instantiates `Reach`

`params` is `Reach.InputParams` counted in sampling periods, `U` among them as in
CORA; `options` is `LinParamSysDT.ReachOptions`. `reachExact` is `reachUnionExact`
over `tFinal - tStart` steps, the system being time-invariant, `reach` is
`reachUnion` (always `some`: nothing here can fail at run time), and the guarantee
is `reachUnion_outer`.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes 𝕄 S]


-- ========================================  INSTANCES  ========================================= --

instance LinParamSysDT.reachInstance :
    Reach (LinParamSysDT 𝕄) (fun n => Reach.InputParams (S n) (S n) ℕ)
      LinParamSysDT.ReachOptions S where
  reachExact sys params := sys.reachUnionExact params.X₀ params.U (params.tFinal - params.tStart)
  reach sys params options := some (sys.reachUnion params options)
  reach_outer sys params options := sys.reachUnion_outer params options

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
