import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# `g ⬝ᵥ w` rounded down, `w` known only to lie in an interval

Split out of `QuadMap.lean` (issue #62): read again by
`Theorems/QuadDownLe.lean`, outside this file.
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

/-- `g ⬝ᵥ w` rounded down, where `w` is known only to lie in `[wlo, whi]`. -/
def PolyZonotope.quadDown (g wlo whi : Vec 𝕋 n) : 𝕋 :=
  sumDown fun r => minimum (mulDown (g r) (wlo r)) (mulDown (g r) (whi r))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
