module

public import CORALean.ContSet.ConZonotope.Real.Operations.LinComb

@[expose] public section

/-!
# `ConZonotope.linComb`'s counts

`linComb`'s generator count: the two operands' plus the one fresh coefficient naming the
interpolation parameter, exactly as a zonotope's `linComb` adds one generator. The equality count
carries over unchanged, `halfScaled` and `comap` both leaving it alone. The inequality count does
grow, by `2(h₁+h₂)`: each block's own unit box, pulled back onto its slice of the concatenated
coefficients; [1, Thm. 5] spends the same `2(h₁+h₂)` slack coefficients as equalities instead. `rfl`
against `Operations/LinComb.lean`, `me` after unfolding the zero the unit box's own equality count
contributes.

## Inputs
* `cZ₁` – first constrained zonotope
* `cZ₂` – second constrained zonotope

## Hypotheses
* none

## Conclusion
* the hull has the sum of the generator counts plus one

## References

* [1] V. Raghuraman and J. P. Koeln. "Set operations and order reductions for
      constrained zonotopes". Automatica, 139:110204, 2022. arXiv:2009.06039.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `h` count of `linComb`'s result. -/
theorem ConZonotope.linComb_h (cZ₁ cZ₂ : ConZonotope α) :
    (cZ₁.linComb cZ₂).h = cZ₁.h + cZ₂.h + 1 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
