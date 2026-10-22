module

public import CORALean.ContSet.ContSet.Definitions.IsFullDim
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# Properties and tests a representation can offer

What the core interfaces leave out because their laws need Mathlib's topology and convexity, stated
over what a representation *denotes*. `CompactSet` is one field, not two: over a normed space
compactness is closed and bounded at once, and it picks the right instances for `inputSolution`.
`ConvexSet` is a property with no data field, independent of `CompactSet` (an `HPolytope` is convex
and not compact, a polynomial zonotope the reverse). `FullDimTest` is CORA's `isFullDim` as a
conservative test: `false` says only that full dimension was not shown.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

/-- Everything this representation denotes is compact. -/
class CompactSet (S : Type) (α : outParam Type) [NormedAddCommGroup α] [NormedSpace ℝ α]
    [ContSet S α] where
  isCompact_construct (s : S) : IsCompact (construct s)

/-- Everything this representation denotes is convex. What an integral valued in
the set needs, and what makes `linComb` a convex hull. -/
class ConvexSet (S : Type) (α : outParam Type) [AddCommGroup α] [Module ℝ α]
    [ContSet S α] where
  convex_construct (s : S) : Convex ℝ (construct s)

/-- A representation with a sound Boolean test for full dimension: `true` means the denoted set has
nonempty interior. -/
class FullDimTest (S : Type) {α : outParam Type} [ContSet S α] [TopologicalSpace α] where
  isFullDim : S → Bool
  isFullDim_sound (s : S) : isFullDim s = true → ContSet.IsFullDim s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
