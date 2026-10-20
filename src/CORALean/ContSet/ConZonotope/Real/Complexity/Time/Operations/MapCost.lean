module

public import CORALean.ContSet.ConZonotope.Real.Operations.Map
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ConZonotope.mapCost`

Asserted, not proved: `Operations/Map.lean` sends the center and each of the `h` generators through
`f` and carries the constraint polytope over untouched, `P := cZ.P`; it is part of the result, so
its `(r + re) * (h + 1)` entries, rows read dense over the `h` coefficients and a right-hand side,
are written.

`plus`, `intersection` and `linComb` each *build* a polytope, counted under the dense-row reading of
`HPolytope.halfScaledCost` (`Complexity/Time/API.lean`). What one `f` costs is a parameter, as in
`PolyZonotope.mapCost`.

## Inputs
* `cf` – cost of the map on one vector
* `h` – number of generators
* `r` – number of inequalities
* `re` – number of equalities

## Output
* the cost of mapping a constrained zonotope
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConZonotope.map` costs at a map costing at most `cf` per application (its write
included) on `h` generators and a polytope of `r`, `re` rows: the applications and the
`(r + re) * (h + 1)` writes of the polytope. -/
def ConZonotope.mapCost (cf : Cost) (h r re : ℕ) : Cost := (h + 1) • cf + ⟨(r + re) * (h + 1)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
