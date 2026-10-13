module

public import CORALean.ContDynamics.NeurNetContrSys.Definitions.WithPeriod
public import CORALean.ContDynamics.NeurNetContrSys.Theorems.ReachUnionOuter
public import CORALean.ContDynamics.Reach.Reach

@[expose] public section

/-!
# `NeurNetContrSys.WithPeriod` instantiates `Reach`

The system with its control period `dt`, CORA's `sys.dt`, since the set a closed
loop reaches depends on it and `reachExact` reads no options. `params` is
`Reach.Params` counted in control periods, `options` `NeurNetContrSys.ReachOptions`.
`reachExact` is `reachUnionExact` over `tFinal - tStart` periods of length `dt`, the
closed loop being time-invariant; `reach` is `reachUnion`, `none` unless
`0 < Δt` and the `N` steps of `Δt` make up exactly `dt` — CORA's check
that `Δt` divides `dt`, decided in ℝ; the guarantee is `reachUnion_outer`.
No input set: the closed loop reads its own input off the controller.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open ContSet

variable {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- ========================================  INSTANCES  ========================================= --

noncomputable instance NeurNetContrSys.WithPeriod.reachInstance :
    Reach (NeurNetContrSys.WithPeriod 𝕋 S) (fun n => Reach.Params (S n) ℕ)
      (NeurNetContrSys.ReachOptions ℝ) S where
  reachExact sys params := sys.sys.reachUnionExact sys.dt (params.tFinal - params.tStart)
    (construct params.X₀)
  reach sys params options :=
    if 0 < options.Δt ∧ (options.N : ℝ) * options.Δt = sys.dt then
      some (sys.sys.reachUnion params options)
    else none
  reach_outer sys params options := by
    split_ifs with h
    · -- the period `reachUnion` steps through is the system's own
      have hout := sys.sys.reachUnion_outer params h.1
      rw [h.2] at hout
      exact hout
    · trivial

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
