import CORALean.ContSet.ContSet.Definitions.IsFullDim

/-!
# `FullDimTest`

CORA's `isFullDim` as a test a representation runs: `true` only if what the set denotes has an
interior point (`ContSet.IsFullDim`). Conservative like `Contains`, so `false` says only that
full dimension was not shown; a float representation certifies its strict comparisons with
`ltStrict` and answers `false` whenever rounding leaves the question open.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet


-- ========================================  MAIN TYPE  ========================================= --

class FullDimTest (S : Type) {α : outParam Type} [ContSet S α] [TopologicalSpace α] where
  isFullDim : S → Bool
  isFullDim_sound (s : S) : isFullDim s = true → ContSet.IsFullDim s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
