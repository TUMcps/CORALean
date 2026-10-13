module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# `LinearSys.verifyRAIntersectionDistanceCora`

CORA's `aux_distanceIntersectionZono` in `@linearSys/private/priv_verifyRA_zonotope.m`:
`w = rad(interval(conZonotope(Z) & P)); dist = 2*sqrt(sum(w.^2))`, the `2`-norm of the diameter of
the interval hull of the intersection. Here in `ℝ¹`, where the interval hull of a set `S` is
`[inf S, sup S]` and `rad` its half-width.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `aux_distanceIntersectionZono` in `ℝ¹`: `2 * sqrt (w ^ 2)` for `w` the radius of the interval
hull `[inf S, sup S]` of the intersection `S`. -/
noncomputable def LinearSys.verifyRAIntersectionDistanceCora (S : Set ℝ) : ℝ :=
  let w := (sSup S - sInf S) / 2                                  -- w = rad(interval(Z & P))
  2 * Real.sqrt (w ^ 2)                                           -- dist = 2*sqrt(sum(w.^2))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
