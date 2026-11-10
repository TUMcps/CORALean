module

public import CORALean.ContSet.Ellipsoid.Real.Theorems.MemToSetIff
public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidConPolyZonoOfFactorToSet

@[expose] public section

/-!
# An ellipsoid as a constrained polynomial zonotope

[1, Prop. 3] with the factor `G = Q^(1/2)` the ellipsoid's own set is defined through, in place of
[1]'s `V √Λ`: the factor form's conversion (`conPolyZonoOfFactor_toSet`) read at `E.G`. Exact,
both directions, with no eigendecomposition paid for it.

## Inputs
* `E` – ellipsoid

## Hypotheses
* none

## Conclusion
* ellipsoid equals its constrained polynomial zonotope

## References

* [1] [N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.](../../../../../../references/2023/kochdumper-constrained-polyzonotopes.md)
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
    E.toSet = E.conPolyZono.toSet :=
  E.toSet_eq_sqrt.trans <| Ellipsoid.conPolyZonoOfFactor_toSet E.G E.q

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
