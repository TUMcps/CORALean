module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Map
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ConPolyZono.mapCost`

Asserted, not proved: `Operations/Map.lean` sends the center and each of the `h` dependent and
`qI` independent generators through `f`, and touches nothing else. What one `f` costs is a
parameter, as in `PolyZonotope.mapCost`, since `f` is any linear map. The exponent matrix and the
constraint block are the operand's but parts of the result, and their entries are written like the
rest.

## Inputs
* `cf` – cost of one application
* `p` – number of factors
* `h` – dependent generators
* `qI` – independent generators
* `m` – number of constraints
* `q` – constraint generators

## Output
* cost of mapping the set
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.map` costs at a map costing at most `cf` per application (its write
included) on `p` factors, `h`, `qI` generators, `m` constraints over `q`: the applications and
`p * h + m * q + m + p * q` writes for the exponent matrix and constraint block. -/
def ConPolyZono.mapCost (cf : Cost) (p h qI m q : ℕ) : Cost :=
  (h + qI + 1) • cf + ⟨p * h + m * q + m + p * q⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
