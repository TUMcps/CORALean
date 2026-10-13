import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBy
import CORALean.Global.Cost

/-!
# `PolyZonotope.reduceByCost`

Asserted, not proved: `Operations/ReduceBy.lean` copies the kept columns of
both blocks and their exponents, which is free here, and builds the diagonal
block from `dropRadius` — one row sum per output coordinate over the `r`
absorbed dependent and `rI` absorbed independent generators, `n * (r + rI)`
absolute values and one addition fewer.

The `n * (n - 1)` off-diagonal zeros are written, not computed, so neither the
kept counts nor the block's own width enter.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.reduceBy` costs at `Vec ℝ n` absorbing `r` dependent and
`rI` independent generators: `2 * n * (r + rI)`, and nothing for what is kept. -/
def PolyZonotope.reduceByCost (n r rI : ℕ) : Cost := ⟨2 * (n * (r + rI))⟩

/-- Monotone in both absorbed counts, so a bound on how many generators a split
throws away gives a bound on the cost. -/
theorem PolyZonotope.reduceByCost_mono {r r' rI rI' : ℕ} (n : ℕ) (hr : r ≤ r') (hI : rI ≤ rI') :
    PolyZonotope.reduceByCost n r rI ≤ PolyZonotope.reduceByCost n r' rI' :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add hr hI))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
