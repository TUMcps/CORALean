module

public import CORALean.ContSet.Polygon.Float.Polygon
public import CORALean.ContSet.VPolytope.Float.Theorems.Basic

@[expose] public section

/-!
# A float polygon is compact

CORA's `polygon/isBounded` returns `true`: a finite union of float polytopes denotes a compact
set, since each does.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.isCompact_construct (P : Polygon 𝕋) :
    IsCompact (ContSet.construct P) := by
  show IsCompact (⋃ s ∈ P.sets, ContSet.construct s)
  exact (List.finite_toSet P.sets).isCompact_biUnion fun p _ => VPolytope.isCompact_construct p

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
