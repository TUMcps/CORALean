module

public import CORALean.ContDynamics.Interfaces
public import CORALean.ContDynamics.NeurNetContrSysDT.Definitions.Linear
public import CORALean.ContDynamics.NeurNetContrSysDT.Theorems.ReachUnionOuter

@[expose] public section

/-!
# `NeurNetContrSysDT` instantiates `Reach`

`params` is `Reach.Params` counted in sampling periods, `options` `NeurNetContrSysDT.ReachOptions`.
`reachExact` is `reachUnionExact` over `tFinal - tStart` steps, the closed loop being
time-invariant, `reach` is `reachUnion` (always `some`: nothing here can fail at run time), and the
guarantee is `reachUnion_outer`, at a `LinearSysDT` plant, the family `NeurNetContrSysDT.Linear`.
The input set is the external `U` the system carries (`U_ext`), the network's part being read off
the controller; and no disturbance, as CORA's loop at a linear plant drops `E`.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]
variable [OfScalarPoint 𝕋 S]


-- ========================================  INSTANCES  ========================================= --

instance NeurNetContrSysDT.reachInstance :
    Reach (NeurNetContrSysDT.Linear 𝕋 S) (fun n _ => Reach.Params (S n) ℕ)
      NeurNetContrSysDT.ReachOptions S where
  reachExact sys params := sys.sys.reachUnionExact (params.tFinal - params.tStart)
    (construct sys.U) (construct params.X₀)
  reach sys params options := some (sys.sys.reachUnion sys.U params options)
  reach_outer sys params options _ h := by
    -- the one set returned is `reachUnion`'s
    cases h
    exact sys.sys.reachUnion_outer sys.U params options

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
