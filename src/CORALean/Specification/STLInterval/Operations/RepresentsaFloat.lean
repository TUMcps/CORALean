module

public import CORALean.Specification.STLInterval.Definitions.RepresentsaType
public import CORALean.Specification.STLInterval.Operations.WithinTolFloat
public import CORALean.Specification.STLInterval.STLInterval

@[expose] public section

/-!
# `representsa_` of an STL interval over a float scalar

`representsa_(I,type,tol)` decided on the stored bounds: the empty set and the `'stlInterval'` type
are decided on the shape, the `'origin'` type by the exact `withinTol` of the bounds, and the
`'point'` type by `withinTol` of the radius, rounded up so that a `true` answer holds for the exact
radius too (`representsaFloat_sound`).

## Inputs
* `tol` – tolerance
* `I` – STL interval
* `type` – set type asked about

## Output
* whether the interval can be represented by the set type, `true` only if it can
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       26-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ExactLe 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `representsa_(I,type,tol)`. -/
def STLInterval.representsaFloat (tol : 𝕋) (I : STLInterval 𝕋)
    (type : STLInterval.RepresentsaType) : Bool :=
  match I, type with
  | .empty, .emptySet => true
  | .empty, .stlInterval => true
  | .empty, _ => false
  | .nonempty .., .stlInterval => true
  | .nonempty .., .emptySet => false
  | .nonempty l u lc rc _ _ _, .point =>
    -- the closed interval, and its radius (rounded up) within the tolerance of zero
    lc && rc && (match u with
      | none => false
      | some u => ExactLe.withinTol tol (half (addUp u (neg l))) zero)
  | .nonempty l u lc rc _ _ _, .origin =>
    -- the closed interval, and both bounds within the tolerance of zero
    lc && rc && STLInterval.withinTolFloat tol (l : WithTop 𝕋) (zero : 𝕋) &&
      STLInterval.withinTolFloat tol u (zero : 𝕋)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
