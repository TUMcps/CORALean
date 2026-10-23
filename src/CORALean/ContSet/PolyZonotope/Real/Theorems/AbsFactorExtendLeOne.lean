module

public import CORALean.ContSet.PolyZonotope.Real.Operations.FactorExtend

@[expose] public section

/-!
# `factorExtend` stays within `[-1, 1]`

Split out of `Compact.lean` (issue #62): reused unchanged by
`ConPolyZono.abs_factorExtend_le_one`, outside this file.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `a` – values of the used factors
* `k` – factor index

## Hypotheses
* `ha` – values are at most one

## Conclusion
* extended value is at most one in absolute value
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.abs_factorExtend_le_one {p h : ℕ} (E : Fin p → Fin h → ℕ)
    {a : Fin (PolyZonotope.usedFactors E).card → ℝ} (ha : ∀ k, |a k| ≤ 1) (k : Fin p) :
    |PolyZonotope.factorExtend E a k| ≤ 1 := by
  rw [PolyZonotope.factorExtend]
  split
  · exact ha _
  · rw [abs_zero]; exact zero_le_one

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
