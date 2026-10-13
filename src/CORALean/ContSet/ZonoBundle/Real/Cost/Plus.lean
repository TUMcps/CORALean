import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
import CORALean.ContSet.Zonotope.Real.Cost.Plus

/-!
# `ZonoBundle.plusCost`

Asserted, not proved: `Operations/Plus.lean` runs `Zonotope.plus` once per pair
of members, `k₁ * k₂` of them, and does nothing of its own.

The product is the whole point of the count. A bundle sum is not a bundle of
sums — each member of one has to be added to each member of the other for the
intersection to be an enclosure — so where a zonotope's `plus` is `n`
additions, a bundle's is `k₁ * k₂ * n`, and two sums in a row square that
again. `Complexity/PlusBigO.lean` is the same fact about the *size* of the
result, in `O`-notation.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ZonoBundle.plus` costs at `Vec ℝ n` on bundles of `k₁` and `k₂`
members: one zonotope sum per pair. -/
def ZonoBundle.plusCost (n k₁ k₂ : ℕ) : Cost := (k₁ * k₂) • Zonotope.plusCost n

/-- Monotone in both member counts, so bounds on the operands' sizes give a
bound on the cost. -/
theorem ZonoBundle.plusCost_mono {k₁ k₁' k₂ k₂' : ℕ} (n : ℕ) (h1 : k₁ ≤ k₁') (h2 : k₂ ≤ k₂') :
    ZonoBundle.plusCost n k₁ k₂ ≤ ZonoBundle.plusCost n k₁' k₂' :=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul h1 h2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
