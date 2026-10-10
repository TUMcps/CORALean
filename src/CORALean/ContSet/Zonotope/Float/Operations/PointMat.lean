import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `GZonotope.pointMat`

A stored matrix as a matrix zonotope: no generators, and the zero box, since nothing
was rounded. The exact layer's `Zonotope.ofPoint`, which `discretizeMatZonotope` feeds
the system matrix through.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   09-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def GZonotope.pointMat (A : Mat 𝕋 m n) : GZonotope (Mat 𝕋 m n) :=
  ⟨0, A, Fin.elim0, Interval.point fun _ _ => zero⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
