module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# Representations that denote a compact set

One field rather than two: an algorithm enclosing an integral needs the set
closed *and* bounded, and over a normed space compactness is exactly both, so
`isClosed_construct` and `isBounded_construct` are theorems here instead of
obligations a representation has to discharge twice.

Compactness rather than the pair also picks the right instances: a merely closed
and bounded representation is one whose affine images need not be closed, and
those are the sets `inputSolution` is built from.

Over a normed space, which is where `IsCompact.isClosed` and
`IsCompact.isBounded` both apply and where every representation instantiating
this already states its lemmas.
-/

-- Authors:       Claude Sonnet 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S α : Type} [NormedAddCommGroup α] [NormedSpace ℝ α] [ContSet S α]


-- ========================================  MAIN TYPE  ========================================= --

/-- Everything this representation denotes is compact. -/
class CompactSet (S : Type) (α : outParam Type) [NormedAddCommGroup α] [NormedSpace ℝ α]
    [ContSet S α] where
  isCompact_construct (s : S) : IsCompact (construct s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
