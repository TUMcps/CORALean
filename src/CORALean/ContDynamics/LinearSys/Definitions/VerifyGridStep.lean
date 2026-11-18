module

public import Mathlib.Data.Fin.Basic

@[expose] public section

/-!
# One step of the grid a zonotope verification pass runs on

The grid comes from CORA's tuning (`priv_reach_adaptive`): the step size, whether the step is
computed in full (some specification is not verified on it yet) or only propagated, and the error
budget of the reduction of the input's generators. None of it decides soundness.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- A step of size `Δt`, in full or propagated only, with the reduction budget. -/
structure LinearSys.VerifyGridStep (𝕋 : Type) where
  /-- The step size. -/
  Δt : 𝕋
  /-- Whether the output set of the step is computed and checked. -/
  full : Bool
  /-- The 2-norm budget of the reduction of the input's generators. -/
  budget : 𝕋

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
