module

public import CORALean.ContSet.Conversion.Real.Operations.ZonoBundle_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Theorems.ConZonotopeConPolyZonoExact
public import CORALean.ContSet.Conversion.Real.Theorems.ZonoBundleConZonotopeAllExact

@[expose] public section

/-!
# CORA's `conPolyZono(zB)` is the bundle

Both steps are exact: `ZonoBundle.conZonotopeAll_exact` and `ConZonotope.conPolyZono_exact`.

## Inputs
* `zB` – zonotope bundle

## Hypotheses
* `hk` – bundle is nonempty

## Conclusion
* constrained polynomial zonotope equals the bundle
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `conPolyZono(conZonotope(zB))` denotes the intersection of the members. -/
theorem ZonoBundle.conPolyZonoAll_exact (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    (zB.conPolyZonoAll hk).construct = zB.construct := by -- --- PROOF ---
  -- `conZonotope(zB)` is the bundle
  have h₁ := zB.conZonotopeAll_exact hk
  -- and its constrained polynomial zonotope is that
  have h₂ := ConZonotope.conPolyZono_exact (zB.conZonotopeAll hk)
  exact h₂.symm.trans h₁

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
