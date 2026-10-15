module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Map
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ConPolyZono.mapCost`

Asserted, not proved: `Operations/Map.lean` sends the centre and each of the
`h` dependent and `qI` independent generators through `f`, and touches nothing
else — the exponent matrix and the whole constraint system, `A`, `b`, `R`,
carry over untouched.

What one `f` costs is a parameter, exactly as in `PolyZonotope.mapCost` and for
the same reason: `f` is any linear map.
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.map` costs at a map costing at most `cf` per application:
one per generator of either block, and one for the centre. -/
def ConPolyZono.mapCost (cf : Cost) (h qI : ℕ) : Cost := (h + qI + 1) • cf

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
