module

public import CORALean.ContSet.Zonotope.Real.Operations.Map
public import CORALean.Global.Cost

@[expose] public section

/-!
# `Zonotope.mapCost`

Asserted, not proved: `Operations/Map.lean` sends the center and each of the
`h` generators through `f`, and touches nothing else.

What one `f` costs is a parameter, as in `PolyZonotope.mapCost` and for the
same reason: `f` is any linear map. `mtimesCost` is this at `Cost.matVec m n`,
the cost of `f := M *ᵥ ·`, though it is stated as its own `def` rather than
through this one. `cf` counts everything one application does, the writes of the vector it
returns included, so no write is added here.

## Inputs
* `cf` – cost of one application of the map
* `h` – generator count

## Output
* one application per generator plus one for the center
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `Zonotope.map` costs at a map costing at most `cf` per application:
one per generator, and one for the center. -/
def Zonotope.mapCost (cf : Cost) (h : ℕ) : Cost := (h + 1) • cf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
