module

public import CORALean.ContSet.VPolytope.Float.Operations.SupportBound
public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.VPolytope_to_HPolytope

@[expose] public section

/-!
# Vertices to halfspaces, over a floating-point scalar

The same conversion as the exact layer's, with the bounds rounded outward: a
dot product per vertex per row, then the largest, then the error box's own reach
in that row added on top.

The rows are copied unchanged into the result, so the halfspace description says
something about the *float* rows it stores rather than about rounded versions of
the caller's intent — which is why nothing here has to round the matrix.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.hPolytope_contains (P : VPolytope (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) :
    P.construct ⊆ (P.hPolytope Aq).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
