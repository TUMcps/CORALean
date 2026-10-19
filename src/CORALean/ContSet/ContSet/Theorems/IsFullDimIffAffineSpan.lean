module

public import CORALean.ContSet.ContSet.Definitions.ConvexSet
public import CORALean.ContSet.ContSet.Definitions.IsFullDim
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

@[expose] public section

/-!
# A convex set is full-dimensional iff its affine hull is everything

CORA's `isFullDim` for every convex representation at once. A convex set in a finite-dimensional
real normed space has an interior point exactly when the affine span of its points is the whole
space (Mathlib's `Convex.interior_nonempty_iff_affineSpan_eq_top`), so a class whose affine hull
it can read off, as a polytope reads it off its vertices, has its `isFullDim` for free.

## Inputs
* `s` – set

## Hypotheses
* none

## Conclusion
* `s` is full-dimensional iff its affine span is everything
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] [FiniteDimensional ℝ α]
  [ContSet S α] [ConvexSet S α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem ContSet.isFullDim_iff_affineSpan (s : S) :
    ContSet.IsFullDim s ↔ affineSpan ℝ (construct s) = ⊤ :=
  (ConvexSet.convex_construct s).interior_nonempty_iff_affineSpan_eq_top

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
