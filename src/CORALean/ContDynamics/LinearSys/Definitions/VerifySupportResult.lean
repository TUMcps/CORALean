module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fin.Basic

@[expose] public section

/-!
# What the support-function verification reports

The verdict of `LinearSys.verifySupportFuncFloat` and CORA's statistics of the run: the number of
passes, the step size and number of steps of the last pass, and for a falsification the time
(exact) and the halfspace.
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The verdict and the statistics of a run over `r` halfspaces. -/
structure LinearSys.VerifySupportResult (𝕋 : Type) (r : ℕ) where
  /-- `some true` verified, `some false` falsified, `none` undecided. -/
  verdict : Option Bool
  /-- CORA's `res.iterations`: the passes, those that did not converge included. -/
  iterations : ℕ
  /-- The step size of the last pass. -/
  timeStep : 𝕋
  /-- The number of steps of the last pass. -/
  nrSteps : ℕ
  /-- The falsifying time and halfspace. -/
  falsification : Option (ℚ × Fin r)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
