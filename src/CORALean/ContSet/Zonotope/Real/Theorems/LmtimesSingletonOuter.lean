module

public import CORALean.ContSet.Zonotope.Real.Operations.LinMtimes
public import CORALean.ContSet.Zonotope.Real.Theorems.MapExact
public import Mathlib.Order.BourbakiWitt

@[expose] public section

/-!
# A one-element set of maps applied to a zonotope

What `LinMtimes` asks of `mapOf`: the union over a singleton is the one map's
image, and that image is exact, so the enclosure holds with nothing to spare.
Stated as an inclusion because that is the shape the interface field has.

## Inputs
* `f` – linear map
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* the image under `f` lies in the mapped zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Reviewed:      16-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- What `LinMtimes` asks of `mapOf`: a set holding one map is that map. -/
theorem Zonotope.lmtimes_singleton_outer (f : α →ₗ[ℝ] β) (Z : Zonotope α) :
    (⋃ g ∈ ({f} : Set (α →ₗ[ℝ] β)), g '' Z.construct) ⊆ (Zonotope.mapOf f Z).construct := by
  refine Set.iUnion₂_subset fun g hg => ?_
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact (Zonotope.map_exact f Z).subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
