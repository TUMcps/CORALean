module

public import CORALean.ContSet.VPolytope.Float.VPolytope

@[expose] public section

/-!
# `VPolytope.matPolytope`, over a floating-point scalar

CORA's `matPolytope(P)`: every vertex read as the `n × 1` matrix with that column. Nothing is
computed on the entries, so nothing rounds: the vertices and the two bounds of the error box are
re-indexed into `Mat 𝕋 n 1`. This is a `VPolytope` of the ambient type `Mat 𝕋 n 1`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.matPolytope (P : VPolytope (Vec 𝕋 n)) : VPolytope (Mat 𝕋 n 1) where
  k := P.k
  V := fun l i _ => P.V l i
  I_error := ⟨fun i _ => P.I_error.inf i, fun i _ => P.I_error.sup i⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
