module

public import CORALean.ContSet.HPolytope.Real.Operations.Ineqs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# `HPolytope.regularPolygon`

The regular `N`-gon inscribed in the disk of radius `R`'s inner approximation: the halfspaces
`cos φₖ x₁ + sin φₖ x₂ ≤ R cos(π/N)` with `φₖ = 2πk/N`. Its vertices lie on the circle of radius
`R`, so the polygon is inside the disk (`HPolytope.regularPolygon_subset_ball`), and the disk of
radius `R cos(π/N)` is inside the polygon.

## Inputs
* `N` – number of sides
* `R` – radius of the disk

## Output
* the polytope of the `N` halfspaces
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The regular `N`-gon of circumradius `R`, as `N` inequalities in the plane. -/
noncomputable def HPolytope.regularPolygon (N : ℕ) (R : ℝ) : HPolytope (Vec ℝ 2) :=
  HPolytope.ineqs
    (fun (k : Fin N) => ![Real.cos (2 * Real.pi * k / N), Real.sin (2 * Real.pi * k / N)])
    (fun _ => R * Real.cos (Real.pi / N))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
