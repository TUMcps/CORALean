module

public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachPolyAdaptivePass
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachPolyAdaptiveState

@[expose] public section

/-!
# The locals of one step of the adaptive `'poly'` outer loop

`LinReachPolyAdaptiveLoop`: as `LinReachAdaptiveLoop`, over `'poly'`'s state and passes.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- The locals of one step's outer loop. -/
structure NonlinearSys.LinReachPolyAdaptiveLoop (𝕋 : Type) (n : ℕ) where
  /-- `options`, as written so far in the step. -/
  st : NonlinearSys.LinReachPolyAdaptiveState 𝕋 n
  /-- `options.timeStep` of this pass. -/
  timeStep : 𝕋
  /-- `finitehorizon`. -/
  finitehorizon : 𝕋
  /-- `error_adm`. -/
  errAdm : Vec 𝕋 n
  /-- `options.run`. -/
  run : ℕ
  /-- `lastStep`. -/
  lastStep : Bool
  /-- `veryfirststep`. -/
  veryfirststep : Bool
  /-- `timeStepequalHorizon`. -/
  timeStepequalHorizon : Bool
  /-- `zetaP`. -/
  zetaP : 𝕋
  /-- `zetaP_h`. -/
  zetaPh : 𝕋
  /-- The pass saved as the horizon's, at its step size. -/
  hor : Option (𝕋 × NonlinearSys.LinReachPolyAdaptivePass 𝕋 n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
