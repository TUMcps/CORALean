import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxExpGreedy
import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.RelaxExpMulti

/-!
# `PolyZonotope.relaxExpGreedyCost`

Asserted, not proved, at `Vec ℝ n`: `Operations/RelaxExpGreedy.lean` runs at most
`N` rounds, each asking the selection `sel` for a pair and applying
`relaxExpMulti` to it. The selection is a parameter of the operation, so its
price `csel` is one here: a round costs at most `csel + relaxExpMultiCost n p`,
and the factor count `p` never changes, a merge keeping it. The generator count
falls by one a round, which the bound ignores.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.relaxExpGreedy` costs at `Vec ℝ n` and `p` factors over
`N` rounds, the selection costing at most `csel` per round. -/
def PolyZonotope.relaxExpGreedyCost (n p N : ℕ) (csel : Cost) : Cost :=
  N • (csel + PolyZonotope.relaxExpMultiCost n p)

/-- Monotone in the round count. -/
theorem PolyZonotope.relaxExpGreedyCost_mono {N N' : ℕ} (n p : ℕ) (csel : Cost) (h : N ≤ N') :
    PolyZonotope.relaxExpGreedyCost n p N csel ≤ PolyZonotope.relaxExpGreedyCost n p N' csel :=
  Nat.mul_le_mul_right _ h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
