module

public import CORALean.ContSet.VPolytope.Real.VPolytope

@[expose] public section

/-!
# `VPolytope.enclosePoints`

CORA's `@polytope/enclosePoints`: the polytope spanned by a finite family of points. CORA runs a
QR reduction and `convhulln` to keep only the extreme points, which changes the vertex list and
not the set; the vertex description of the whole family denotes the same hull.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.enclosePoints {N : ℕ} (pts : Fin N → Vec ℝ n) : VPolytope (Vec ℝ n) :=
  ⟨N, pts⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
