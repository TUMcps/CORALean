module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Map
public import CORALean.Global.Cost

@[expose] public section

/-!
# `ConPolyZono.mapCost`

Asserted, not proved: `Operations/Map.lean` sends the center and each of the
`h` dependent and `qI` independent generators through `f`, and touches nothing
else — the exponent matrix and the whole constraint system, `A`, `b`, `R`,
carry over untouched.

What one `f` costs is a parameter, exactly as in `PolyZonotope.mapCost` and for
the same reason: `f` is any linear map.

The exponent matrix and the constraint block are the operand's, but they are parts of the result,
and their entries are written like the rest.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       23-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What `ConPolyZono.map` costs at a map costing at most `cf` per application (its write
included) on `p` factors, `h`, `qI` generators, `m` constraints over `q`: the applications and
`p * h + m * q + 2 * m + p * q` writes for the exponent matrix and constraint block. -/
def ConPolyZono.mapCost (cf : Cost) (p h qI m q : ℕ) : Cost :=
  (h + qI + 1) • cf + ⟨p * h + m * q + 2 * m + p * q⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
