import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.ContSet.Zonotope.Float.Operations.ListQuadUp

/-!
# `Zonotope.cubFoldUp`

The coefficient `Zonotope.cubFold` of the sorted triple of extended columns `[c, G]`, in `𝕋`,
rounded up: the accumulation over identical factors of `Zonotope.listQuadUp`, every sum rounded
the same way.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.cubFoldUp (T : Fin m → Fin n → Mat 𝕋 n n) (Z : Zonotope 𝕋 n) (i : Fin m)
    (x y z : Fin (Z.h + 1)) : 𝕋 :=
  -- `[c, G]`
  let Zext : Fin (Z.h + 1) → Vec 𝕋 n := Fin.cons Z.c Z.G
  -- the accumulation of identical factors
  addUp (addUp (Zonotope.listQuadUp T Zext i x y z)
      (if x < z then Zonotope.listQuadUp T Zext i z x y else zero))
    (if x < y ∧ y < z then Zonotope.listQuadUp T Zext i y x z else zero)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
