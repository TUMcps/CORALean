import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilDown
import CORALean.ContSet.ConZonotope.Float.Operations.QuadBilUp

/-!
# `ConZonotope.quadMapCUp`

The centre of `quadMapCDown` rounded up; the box the stored centre needs is the gap
between the two.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The centre of the enclosing zonotope, from above. -/
def ConZonotope.quadMapCUp (Q : Fin m → Mat 𝕋 n n) (cZ : ConZonotope 𝕋 n) : Vec 𝕋 m :=
  fun i => addUp (ConZonotope.quadBilUp (Q i) cZ.c cZ.c)
    (half (sumUp fun s => ConZonotope.quadBilUp (Q i) (fun r => cZ.G r s) fun r => cZ.G r s))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
