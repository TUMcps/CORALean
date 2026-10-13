import CORALean.ContSet.Zonotope.Real.Operations.ReduceByBasis
import CORALean.ContSet.Zonotope.Real.Complexity.Time.ReduceBy

/-!
# `Zonotope.reduceByBasisCost`

Asserted, not proved: `Operations/ReduceByBasis.lean` inverts the basis `P`, a
numerical routine the definition names only as `P⁻¹`, so its price `inv` is a
parameter, as `mapCost` takes what one application of `f` costs. Then each of
the `r` absorbed generators goes through `P⁻¹ *ᵥ ·` (`Cost.matVec n n`), each
of the `n` output rows sums `r` absolute values (`2 * n * r`), and each column
of `P` is scaled by its sum (`n * n`).
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.reduceByBasis` costs at `Vec ℝ n` absorbing `r` generators,
the inverse costing at most `inv`. -/
def Zonotope.reduceByBasisCost (n r : ℕ) (inv : Cost) : Cost :=
  inv + r • Cost.matVec n n + ⟨2 * (n * r) + n * n⟩

/-- Monotone in the absorbed count. -/
theorem Zonotope.reduceByBasisCost_mono {r r' : ℕ} (n : ℕ) (inv : Cost) (hr : r ≤ r') :
    Zonotope.reduceByBasisCost n r inv ≤ Zonotope.reduceByBasisCost n r' inv := by
  have := Nat.mul_le_mul_right (2 * (n * n)) hr
  have := Nat.mul_le_mul_left n hr
  simp only [Zonotope.reduceByBasisCost, Cost.le_iff, Cost.ops_add, Cost.ops_smul, Cost.matVec]
  omega

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
