module

public import CORALean.ContDynamics.NeurNetContrSys.Definitions.Linear
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.Interfaces

@[expose] public section

/-!
# `NeurNetContrSys.Linear` instantiates `Reach`

The system carries its control period `dt`, CORA's `sys.dt`, since the set a closed loop reaches
depends on it and `reachExact` reads no options. `params` is `Reach.Params` counted in control
periods, `options` `NeurNetContrSys.ReachOptions`. `reachExact` is `reachUnionExact` over
`tFinal - tStart` periods of length `dt`; `reach` is `reachUnion`, `none` unless `0 < Δt` and the
`N` steps of `Δt` make up exactly `dt`, CORA's check that `Δt` divides `dt`, decided in ℝ; the
guarantee is `reachUnion_outer`. The input set is the external `U` the system carries (`U_ext`),
and no disturbance, `W = {0}`, as CORA's loop at a linear plant drops `E`.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       24-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S] [∀ n, OfPoint (S n) (Vec ℝ n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance NeurNetContrSys.Linear.reachInstance :
    Reach (NeurNetContrSys.Linear 𝕋 S) (fun n _ => Reach.Params (S n) ℕ)
      (NeurNetContrSys.ReachOptions ℝ) S where
  reachExact sys params := sys.sys.reachUnionExact (params.tFinal - params.tStart)
    (construct sys.U) {0} (construct params.X₀)
  reach sys params options :=
    if 0 < options.Δt ∧ (options.N : ℝ) * options.Δt = sys.sys.dt then
      some (sys.sys.reachUnion sys.U params options)
    else none
  reach_outer sys params options _ hR := by
    split_ifs at hR with h
    cases hR
    -- the period `reachUnion` steps through is the system's own
    exact sys.sys.reachUnion_outer sys.U params h.2.symm h.1

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
