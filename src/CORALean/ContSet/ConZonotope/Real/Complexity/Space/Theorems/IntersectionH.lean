module

public import CORALean.ContSet.ConZonotope.Real.Operations.Intersection

@[expose] public section

/-!
# `ConZonotope.intersection`'s counts

`intersection`'s generator count concatenates, as `plus`'s does. The inequality count
concatenates too, `comap` and `intersection` costing nothing beyond what each operand's
`P` already had; the equality count carries one further block, `n` rows
pinning the two generator blocks together coordinate by coordinate — the one
constraint list `intersection` builds beyond what `plus` needs. `rfl` against the
structure instance in `Operations/Intersection.lean`.

## Inputs
* `cZ₁` – first constrained zonotope
* `cZ₂` – second constrained zonotope

## Hypotheses
* none

## Conclusion
* the intersection has the sum of the generator counts
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `h` count of `intersection`'s result. -/
theorem ConZonotope.intersection_h (cZ₁ cZ₂ : ConZonotope (Vec ℝ n)) :
    (cZ₁.intersection cZ₂).h = cZ₁.h + cZ₂.h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
