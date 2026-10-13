import CORALean.ContSet.Polygon.Float.Polygon

/-!
# `Polygon.vertices`, over a floating-point scalar

CORA's `polygon/vertices_`, as the exact layer: the stored vertices of every piece (the columns of
each piece's vertex matrix). Each piece carries an error box besides, which these vertices do not
include: `Polygon.vertices_outer` says where the polygon lies relative to them.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def Polygon.vertices (P : Polygon 𝕋) : List (Vec 𝕋 2) :=
  P.sets.flatMap fun p => List.ofFn fun l : Fin p.k => p.V l

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
