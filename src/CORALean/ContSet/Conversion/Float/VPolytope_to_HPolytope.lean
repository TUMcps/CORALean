import CORALean.ContSet.VPolytope.Float.Operations.SupportBound
import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
import CORALean.ContSet.HPolytope.Float.Operations.SubsetOfBounds

/-!
# Vertices to halfspaces, over a floating-point scalar

The same conversion as the exact layer's, with the bounds rounded outward: a
dot product per vertex per row, then the largest, then the error box's own reach
in that row added on top.

The rows are copied unchanged into the result, so the halfspace description says
something about the *float* rows it stores rather than about rounded versions of
the caller's intent — which is why nothing here has to round the matrix.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {q n : ℕ}

def VPolytope.hPolytope (P : VPolytope (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) : HPolytope 𝕋 (Vec 𝕋 n) :=
  HPolytope.ofBounds Aq fun i => P.boundDot (Aq i) fun _ => rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.hPolytope_contains (P : VPolytope (Vec 𝕋 n)) (Aq : Mat 𝕋 q n) :
    P.construct ⊆ (P.hPolytope Aq).construct :=
  HPolytope.subset_ofBounds _ _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
