module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
public import CORALean.ContSet.PolyZonotope.Real.Theorems.PadBackPoint

@[expose] public section

/-!
# `padBack` carries a factor sub-box back through the appended factors

`padBack_point` composed, the mirror of `padFront_subsetAt`: the padded set at
`B` is the original set at `B` read through `Fin.castAdd r`, the reindexing map
`padBack_point` reads each point through, dropping the `r` appended factors.

`padBack` preserves `p` only up to `(pZ.padBack r).p = pZ.p + r`, but that
equation is `rfl` — a structure-literal field, as for `padFront`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `padBack`'s subset at `B` is the original subset at `B` reindexed through
the dropped suffix. -/
theorem PolyZonotope.padBack_subsetAt (r : ℕ) (pZ : PolyZonotope α)
    (B : Set (Fin (pZ.p + r) → ℝ)) :
    (pZ.padBack r).subsetAt B = pZ.subsetAt ((· ∘ Fin.castAdd r) '' B) := by
  show (pZ.padBack r).point '' B = pZ.point '' ((· ∘ Fin.castAdd r) '' B)
  rw [← Set.image_comp]
  exact Set.image_congr fun a _ => PolyZonotope.padBack_point r pZ a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
