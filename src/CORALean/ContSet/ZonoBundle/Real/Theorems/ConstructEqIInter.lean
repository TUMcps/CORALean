module

public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
public import CORALean.ContSet.SetIntersection.Theorems.Basic

@[expose] public section

/-!
# A bundle denotes the intersection over its index

`ZonoBundle.construct` is `SetIntersection`'s intersection of the listed members by definition;
this reads it back over `Fin k` with each member's own `Zonotope.construct`, through the general
`SetIntersection.construct_ofFn`. It is the form a proof about one of CORA's algorithms, which
names members by their index, starts from.

## Inputs
* `zB` – zonotope bundle

## Hypotheses
* none

## Conclusion
* the bundle denotes the intersection of its members
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- A bundle denotes the intersection of its members over their index. -/
theorem ZonoBundle.construct_eq_iInter (zB : ZonoBundle α) :
    zB.construct = ⋂ i, (zB.Z i).construct :=
  SetIntersection.construct_ofFn zB.Z

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
