module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PadFrontPoint

@[expose] public section

/-!
# `padFront` carries a factor sub-box back through the prepended factors

`padFront_point` composed: the padded set at `B` is the original set at `B`
read through the same reindexing map `padFront_point` reads each point
through, `Fin.natAdd l` dropping the `l` prepended factors.

`padFront` preserves `p` only up to the equation `(pZ.padFront l).p = l + pZ.p`,
but that equation is `rfl` — `p` is set by a structure literal, so the
projection reduces without a cast, exactly as `map_subsetAt` needs none.

## Inputs
* `l` – number of added factors
* `pZ` – polynomial zonotope
* `B` – box of factor values

## Hypotheses
* none

## Conclusion
* subset at the box is the original subset at the restricted box
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `padFront`'s subset at `B` is the original subset at `B` reindexed through
the dropped prefix. -/
theorem PolyZonotope.padFront_subsetAt (l : ℕ) (pZ : PolyZonotope α)
    (B : Set (Fin (l + pZ.p) → ℝ)) :
    (pZ.padFront l).subsetAt B = pZ.subsetAt ((· ∘ Fin.natAdd l) '' B) := by
  show (pZ.padFront l).point '' B = pZ.point '' ((· ∘ Fin.natAdd l) '' B)
  rw [← Set.image_comp]
  exact Set.image_congr fun a _ => PolyZonotope.padFront_point l pZ a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
