import CORALean.ContDynamics.NonlinearSys.Definitions.RelinReachOptions

/-!
# CORA's `options` for the differences of the re-linearization loop

`RelinReachOptions` and CORA's `taylorTerms`, the order the differences' input
solution is taken at (the paper's `η`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       30-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- `RelinReachOptions`, and the Taylor order `η` of the differences. -/
structure NonlinearSys.RelinDeltaReachOptions extends NonlinearSys.RelinReachOptions where
  η : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
