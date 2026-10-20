module

public import CORALean.ContSet.Zonotope.Real.Operations.OfPoint
public import CORALean.ContSet.ZonoBundle.Real.ZonoBundle

@[expose] public section

/-!
# `ZonoBundle.ofPoint`

A bundle of one zonotope, itself a point: `k = 1`, the single member
`Zonotope.ofPoint v`. What `OfPoint` asks every representation with a point
operation to supply.

## Inputs
* `v` – point

## Output
* the single-point bundle
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A single point, as a bundle of one zonotope with no generators. -/
def ZonoBundle.ofPoint (v : α) : ZonoBundle α := ⟨1, fun _ => Zonotope.ofPoint v⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
