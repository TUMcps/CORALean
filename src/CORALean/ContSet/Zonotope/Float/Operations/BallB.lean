import CORALean.Global.Float.FloatOps

/-!
# `Zonotope.ballB`

A candidate radius for the box a certified right inverse `H` reaches: a quarter of `δ` over the
largest absolute row sum of `H`, rounded down. Nothing is trusted about it: `Zonotope.ballCert`
checks the radius it is given, so a bad candidate (a zero row sum, say) only costs the `true`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n h : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.ballB (H : Mat 𝕋 h n) (δ : 𝕋) : 𝕋 :=
  let M := maximumOver (radius H)
  divDown δ (addUp (addUp M M) (addUp M M))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
