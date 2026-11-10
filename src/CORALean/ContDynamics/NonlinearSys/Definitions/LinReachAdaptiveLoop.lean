module

public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachAdaptivePass
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachAdaptiveState

@[expose] public section

/-!
# The outer loop of one adaptive step

`LinReachAdaptiveLoop`: the locals of `linReach_adaptive`'s outer `while true` loop, the `options`
it has written so far in the step, and the pass saved as the horizon's (`Rerror_h`, `Rti_h`,
`Rtp_h`) with its step size and `zetaP_h`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- The locals of one step's outer loop. -/
structure NonlinearSys.LinReachAdaptiveLoop (𝕋 : Type) (n : ℕ) where
  /-- `options`, as written so far in the step. -/
  st : NonlinearSys.LinReachAdaptiveState 𝕋 n
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
  hor : Option (𝕋 × NonlinearSys.LinReachAdaptivePass 𝕋 n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
