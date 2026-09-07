import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetPoint

/-!
# `getSubset` carries a factor sub-box to the corresponding subset

`getSubset_point` composed into `subsetAt`, the way `map_subsetAt` composes
`map_point`: what the new factors reach over `B` is what the old ones reached
over `B`'s image under `βₖ ↦ cen + rad·βₖ`. An equality for every `B`, with no
hypothesis at all — neither on `rad`, nor on the independent block, nor on the
degree.

`getSubset` leaves `p` alone, so `B` needs no transport here, as with `map` and
unlike a chain through `bilin` or `padFront`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `getSubset`'s subset at `B` is the original's at the re-parametrized `B`. -/
theorem PolyZonotope.getSubset_subsetAt (pZ : PolyZonotope α) (k : Fin pZ.p) (cen rad : ℝ)
    (B : Set (Fin pZ.p → ℝ)) : (pZ.getSubset k cen rad).subsetAt B
      = pZ.subsetAt ((fun b => Function.update b k (cen + rad * b k)) '' B) := by
  show (pZ.getSubset k cen rad).point '' B = pZ.point '' (_ '' B)
  rw [← Set.image_comp]
  exact Set.image_congr fun b _ => pZ.getSubset_point k cen rad b

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
