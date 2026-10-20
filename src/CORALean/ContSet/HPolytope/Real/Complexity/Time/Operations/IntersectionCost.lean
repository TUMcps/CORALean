module

public import CORALean.ContSet.HPolytope.Real.Operations.Intersection
public import CORALean.Global.Cost

@[expose] public section

/-!
# `HPolytope.intersectionCost`

Asserted, not proved, and no longer zero: `Operations/Intersection.lean` is six calls to
`Fin.append`, one per field, which computes nothing. Under `Global/Cost.lean`'s model the result
is still a new polytope whose rows are all written, read, as `halfScaledCost` reads them, as dense
vectors of length `d`: the `m₁ + m₂` inequality and `me₁ + me₂` equality rows of `d` coefficients
and a right-hand side each.

## Inputs
* `d` – natural number
* `m₁` – natural number
* `m₂` – natural number
* `me₁` – natural number
* `me₂` – natural number

## Output
* one write for each of the `(m₁ + m₂ + me₁ + me₂) * (d + 1)` entries of the result
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `HPolytope.intersection` costs over a coefficient space of dimension `d`, the operands
holding `mᵢ` inequality and `meᵢ` equality rows: one write for each of the
`(m₁ + m₂ + me₁ + me₂) * (d + 1)` entries of the result. -/
def HPolytope.intersectionCost (d m₁ m₂ me₁ me₂ : ℕ) : Cost :=
  ⟨(m₁ + m₂ + me₁ + me₂) * (d + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
