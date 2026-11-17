module

public import Mathlib.Data.Fin.Basic

@[expose] public section

/-!
# What one pass of the support-function verification ends with

A pass of `LinearSys.verifySupportPassFloat` at a fixed step size either cannot run at it (a
correction matrix or the exponential is not enclosed: the step shrinks), cannot bound the growth of
the propagated directions at all, finds a time point whose distance from below is positive (a
falsification), or decides every step of every halfspace, verified or not.
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- The end of one pass over `r` halfspaces. -/
inductive LinearSys.VerifySupportOutcome (r : ℕ) where
  /-- `F` or `e^{AΔt}` is not enclosed at this step size. -/
  | notConverged
  /-- The step size is not positive or the growth bound of the directions is not computable. -/
  | noBound
  /-- The time point `k Δt` violates halfspace `q`. -/
  | falsified (k : ℕ) (q : Fin r)
  /-- For each step, in order, which halfspaces hold over it. -/
  | decided (flags : List (Fin r → Bool))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
