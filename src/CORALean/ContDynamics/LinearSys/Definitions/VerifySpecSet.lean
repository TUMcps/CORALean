module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# A safe or an unsafe set of the zonotope verification

The halfspaces `a' y ≤ b` of one specification in the output space: a safe set must contain every
output, an unsafe set (their intersection) must meet none. CORA's unsafe set of one halfspace is
the safe set of the complementary one, `-a' y < -b`, which the caller passes as a safe set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float


-- ========================================  MAIN TYPE  ========================================= --

/-- The rows `(a, b)` of `a' y ≤ b`, and whether they bound a safe or an unsafe set. -/
structure LinearSys.VerifySpecSet (𝕋 : Type) (q : ℕ) where
  /-- `true` for a safe set, `false` for an unsafe one. -/
  safe : Bool
  /-- The halfspaces. -/
  rows : List (Vec 𝕋 q × 𝕋)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
