module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemConstructIff
public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidConPolyZonoOfFactorConstruct

@[expose] public section

/-!
# An ellipsoid as a constrained polynomial zonotope

[1, Prop. 3] with the factor `G = Q^(1/2)` the ellipsoid's own set is defined through, in place of
[1]'s `V √Λ`: the factor form's conversion (`conPolyZonoOfFactor_construct`) read at `E.G`. Exact,
both directions, with no eigendecomposition paid for it.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       12-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Ellipsoid.conPolyZono_exact (E : Ellipsoid n) :
    E.construct = E.conPolyZono.construct :=
  E.construct_eq_sqrt.trans <| Ellipsoid.conPolyZonoOfFactor_construct E.G E.q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
