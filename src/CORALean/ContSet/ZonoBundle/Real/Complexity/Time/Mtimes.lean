import CORALean.ContSet.ZonoBundle.Real.Operations.Mtimes
import CORALean.ContSet.Zonotope.Real.Complexity.Time.Mtimes

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

/-- Monotone in the member count and in the generator bound, so bounds on the
operand's sizes give a bound on the cost. -/
theorem ZonoBundle.mtimesCost_mono {k k' h h' : ℕ} (m n : ℕ) (hk : k ≤ k') (hh : h ≤ h') :
    ZonoBundle.mtimesCost m n k h ≤ ZonoBundle.mtimesCost m n k' h' :=
  Nat.mul_le_mul hk (Cost.le_iff.mp (Zonotope.mtimesCost_mono m n hh))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
