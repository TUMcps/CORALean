module

public import CORALean.ContSet.Conversion.Real.Theorems.HPolytopeConPolyZonoExact

@[expose] public section

/-!
# A halfspace description as a constrained polynomial zonotope

CORA's `conPolyZono(conZonotope(P))` is exact (`HPolytope.conPolyZono_exact`), so it holds `P`.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.conPolyZono_contains (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) :
    P.construct ⊆ (HPolytope.conPolyZono up lo).construct :=
  (HPolytope.conPolyZono_exact up lo).symm.subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
