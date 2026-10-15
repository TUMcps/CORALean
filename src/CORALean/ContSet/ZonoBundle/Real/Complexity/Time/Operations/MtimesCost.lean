module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Complexity.Time.Operations.MtimesCost

@[expose] public section

/-!
# `ZonoBundle.mtimesCost`

Asserted, not proved: `Operations/Mtimes.lean` runs `Zonotope.mtimes` once per
member and does nothing of its own, so the count is `k` copies of the zonotope
one.

`h` is a bound on *every* member's generator count rather than any one member's,
since the structure carries a family of zonotopes and no common width. That is
what keeps this an upper bound; a caller with a per-member count sums those
instead, and gets something smaller and less composable.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ZonoBundle.mtimes` costs at `M : Mat ℝ m n` on a bundle of `k`
members, none of them over `h` generators. -/
def ZonoBundle.mtimesCost (m n k h : ℕ) : Cost := k • Zonotope.mtimesCost m n h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
