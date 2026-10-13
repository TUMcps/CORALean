import CORALean.ContSet.VPolytope.Float.VPolytope

/-!
# `VPolytope.matPolytope`, over a floating-point scalar

CORA's `matPolytope(P)`: every vertex read as the `n × 1` matrix with that column. Nothing is
computed on the entries, so nothing rounds: the vertices and the two bounds of the error box are
re-indexed into `Mat 𝕋 n 1`. This is a `VPolytope` of the ambient type `Mat 𝕋 n 1`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.matPolytope (P : VPolytope (Vec 𝕋 n)) : VPolytope (Mat 𝕋 n 1) where
  k := P.k
  V := fun l i _ => P.V l i
  E := ⟨fun i _ => P.E.inf i, fun i _ => P.E.sup i⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
