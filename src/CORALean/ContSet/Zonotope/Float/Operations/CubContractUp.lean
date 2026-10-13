module

public import CORALean.ContSet.Zonotope.Float.Operations.CubContractDown

@[expose] public section

/-!
# `Zonotope.cubContractUp`, the cubic contraction of three vectors rounded up

`Zonotope.cubContractDown` rounded the other way: a float above `Σₖ uₖ · (vᵀ T{i,k} w)`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A float above `Σₖ uₖ · (vᵀ T{i,k} w)`. -/
def Zonotope.cubContractUp (T : Fin m → Fin n → Mat 𝕋 n n) (u v w : Vec 𝕋 n) (i : Fin m) :
    𝕋 :=
  let qLo := fun k => PolyZonotope.quadDown v (mulVecDown (T i k) w) (mulVecUp (T i k) w)
  let qHi := fun k => PolyZonotope.quadUp v (mulVecDown (T i k) w) (mulVecUp (T i k) w)
  PolyZonotope.quadUp u qLo qHi

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
