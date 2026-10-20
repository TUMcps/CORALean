module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Intersection

@[expose] public section

/-!
# `ConPolyZono.intersection`'s counts

`intersection` runs `intersectionDep` on the two `dependent` sets: every independent generator is
freed into a factor first, so the two operands' `p` and `h` each carry their
own `qI` along before the two combine, the independent block empties, `m` picks
up one row per output coordinate, and `q` gains one constraint generator per
freed dependent generator. `rfl` by unfolding `dependent` and `intersectionDep` rather
than restating either.

## Inputs
* `cPZ₁` – first operand
* `cPZ₂` – second operand

## Hypotheses
* none

## Conclusion
* the factor count of the intersection is the sum of both operands' factor counts
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `p` count of `intersection`'s result. -/
theorem ConPolyZono.intersection_p (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.intersection cPZ₁ cPZ₂).p = (cPZ₁.p + cPZ₁.qI) + (cPZ₂.p + cPZ₂.qI) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
