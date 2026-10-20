module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Map
public import CORALean.Global.Cost

@[expose] public section

/-!
# `PolyZonotope.mapCost`

Asserted, not proved: `Operations/Map.lean` sends the center, each of the `h` dependent
generators and each of the `q` independent ones through `f`, and touches nothing else; the
exponent matrix is carried over whole, its `p * h` entries written like the rest. What one `f`
costs is a parameter, `cf` a bound on one application, `f` being any linear map; `mtimesCost`
is this at `cf := Cost.matVec m n`. A caller with no bound on `f` has no bound here either.

## Inputs
* `cf` – cost of mapping one vector
* `p` – number of factors
* `h` – dependent generator count
* `q` – independent generator count

## Output
* operation count of the linear map
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `PolyZonotope.map` costs at a map costing at most `cf` per application (its write
included) on `p` factors, `h`, `q` generators: the applications and the `p * h` writes of the
exponent matrix. -/
def PolyZonotope.mapCost (cf : Cost) (p h q : ℕ) : Cost := (h + q + 1) • cf + ⟨p * h⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
