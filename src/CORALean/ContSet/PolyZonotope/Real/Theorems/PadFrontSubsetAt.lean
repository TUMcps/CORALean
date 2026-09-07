import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.PadFrontPoint

/-!
# `padFront` carries a factor sub-box back through the prepended factors

`padFront_point` composed: the padded set at `B` is the original set at `B`
read through the same reindexing map `padFront_point` reads each point
through, `Fin.natAdd l` dropping the `l` prepended factors.

`padFront` preserves `p` only up to the equation `(S.padFront l).p = l + S.p`,
but that equation is `rfl` — `p` is set by a structure literal, so the
projection reduces without a cast, exactly as `map_subsetAt` needs none.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `padFront`'s subset at `B` is the original subset at `B` reindexed through
the dropped prefix. -/
theorem PolyZonotope.padFront_subsetAt (l : ℕ) (S : PolyZonotope α)
    (B : Set (Fin (l + S.p) → ℝ)) :
    (S.padFront l).subsetAt B = S.subsetAt ((· ∘ Fin.natAdd l) '' B) := by
  show (S.padFront l).point '' B = S.point '' ((· ∘ Fin.natAdd l) '' B)
  rw [← Set.image_comp]
  exact Set.image_congr fun a _ => PolyZonotope.padFront_point l S a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
