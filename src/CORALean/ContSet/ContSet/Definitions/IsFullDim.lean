module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Topology.Basic

@[expose] public section

/-!
# `ContSet.IsFullDim`

CORA's `isFullDim`, stated once for every representation: what it denotes has an interior point.
The topology is the ambient type's, so at `Vec ℝ n` it is the usual one and "full-dimensional"
means what it says. Each class then characterises it (`Interval.isFullDim_iff`, ...).
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S α : Type} [ContSet S α] [TopologicalSpace α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The set `s` denotes has a nonempty interior. -/
def ContSet.IsFullDim (s : S) : Prop := (interior (construct s)).Nonempty

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
