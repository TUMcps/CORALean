module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.convHullCora`: `convHull_` as CORA's code runs, an empty second operand included

`@ellipsoid/convHull_.m` opens the case of an empty second operand with

```
% convex hull with empty set
if representsa_(S,'emptySet',eps)
    return;
end
```

(l. 56-58) and never assigns `S_out` before that `return`: MATLAB stops with `Output argument
'S_out' (and maybe others) not assigned during call`. The result for an ellipsoid and another
ellipsoid is `or(E,S,'outer')`, an SDP-solver result, taken here as a parameter `orOuter`. Read
from the source, not run.

The model has no empty ellipsoid, so `ellipsoid.empty(n)` is `none` in the second operand.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `S_out = convHull_(E, S)` for ellipsoids, `S = none` standing for
`ellipsoid.empty(n)`; `none` as a result is the MATLAB error. -/
def Ellipsoid.convHullCora (orOuter : Ellipsoid n → Ellipsoid n → Ellipsoid n)
    (E : Ellipsoid n) (S : Option (Ellipsoid n)) : Option (Ellipsoid n) :=
  match S with
  -- representsa_(S,'emptySet',eps): `return` with `S_out` never assigned
  | none => none
  -- isa(S,'ellipsoid'): S_out = or(E,S,'outer')
  | some S' => some (orOuter E S')

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
