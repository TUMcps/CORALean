import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSum
import CORALean.ContSet.PolyZonotope.Real.Operations.Rep

/-!
# The columns `compact` keeps

Split out of `Compact.lean` (issue #62): used again by `compactIdx` and
`compactGens` below, by `Theorems/CompactGensExact.lean`, and by
`ConPolyZono`'s own compaction over `EC`, all outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The columns that survive: those whose merged generator is not zero. A column
that is not its class's representative has an empty fibre and so is dropped here
too, which is why merging and zero-dropping are one step. -/
noncomputable def PolyZonotope.compactKeep {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (G : Fin h → α) : Finset (Fin h) :=
  @Finset.filter _ (fun j => PolyZonotope.fiberSum (PolyZonotope.rep E) G j ≠ 0)
    (Classical.decPred _) Finset.univ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
