module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# One direction of a Krylov verification pass

A halfspace `w' x ≤ d` (non-strict, a safe set's row) or `w' x < d` (strict, a row of an unsafe
set, negated) in the state space, with the plan of the restart windows of `w' e^{tA}` (the order
and the steps of each, CORA.cpp's tuning). The directions of a
specification share a group: a safe set has one group per row, all of which must hold; an unsafe
set one group for all its rows, one of which must hold on a step.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- A direction `w`, its windows' plan, the limit `d` of `w' x`, whether it is strict, and its
group. -/
structure LinearSys.VerifyKrylovDirection (𝕋 : Type) (n : ℕ) where
  /-- The direction in the state space. -/
  w : Vec 𝕋 n
  /-- The order and the steps of `Δt₀` of every restart window of `w' e^{tA}`. -/
  plan : List (ℕ × ℕ)
  /-- The limit of `w' x`. -/
  limit : 𝕋
  /-- `w' x < limit` if `true`, else `w' x ≤ limit`. -/
  strict : Bool
  /-- The group of the direction: one direction of every group must hold on every step. -/
  group : ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
