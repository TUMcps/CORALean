module

public import CORALean.ContSet.Conversion.Real.Operations.ConZonotope_to_ConPolyZono
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_ConZonotope

@[expose] public section

/-!
# A halfspace description as a constrained polynomial zonotope, as CORA's `conPolyZono(P)`

`@polytope/conPolyZono.m` is `conPolyZono(conZonotope(P))`: the polytope's constrained zonotope,
whose box comes from the support bounds `up`, `lo` (CORA's `'exact:supportFunc'` with
`B = interval(P)`), read as a constrained polynomial zonotope. Both steps are exact.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ} {P : HPolytope (Vec ℝ n)}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `conPolyZono(P)`: `conPolyZono(conZonotope(P))`. -/
noncomputable def HPolytope.conPolyZono (up : ∀ j, SupportBound P.construct (LinearMap.proj j))
    (lo : ∀ j, SupportBound P.construct (-LinearMap.proj j)) : ConPolyZono (Vec ℝ n) :=
  -- `conZonotope(P)`, the box from the support bounds
  let cZ := HPolytope.conZonotope up lo
  -- `conPolyZono(cZ)`
  cZ.conPolyZono

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
