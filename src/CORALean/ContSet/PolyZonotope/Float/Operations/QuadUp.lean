import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `g ⬝ᵥ w` rounded up, `w` known only to lie in an interval

Split out of `QuadMap.lean` (issue #62): read again by
`Theorems/LeQuadUp.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.quadUp (g wlo whi : Vec 𝕋 n) : 𝕋 :=
  sumUp fun r => maximum (mulUp (g r) (wlo r)) (mulUp (g r) (whi r))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
