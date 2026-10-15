module

public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.Ellipsoid.Float.Operations.IsPsd

@[expose] public section

/-!
# `Ellipsoid.containsPoint`, over a floating-point scalar

CORA's `@ellipsoid/contains_` for a point, as a check of a caller-proposed certificate: CORA solves
`Q \ (p - q)`; a float solve is not exact, so the solve is the caller's and only its result `w` is
checked. `Q` certified positive semi-definite (`isPsd`, without which the nominal part is only the
center), `wᵀ Q w ≤ 1` from above (`quadUp`), and the remainder `p - q - Q w`, bracketed by
directed roundings, inside the error box: then `q + Q w` is a point of the nominal ellipsoid
(`Real.Ellipsoid.add_mulVec_mem_construct`). Only `true` is certain; `false` says only that this
`w` does not show membership.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.containsPoint (E : Ellipsoid 𝕋 n) (p w : Vec 𝕋 n) : Bool :=
  -- the remainder `p - q - Q w`, between its two roundings
  let lo : Vec 𝕋 n := fun i => subDown (p i) (addUp (E.q i) (mulVecUp E.Q w i))
  let hi : Vec 𝕋 n := fun i => subUp (p i) (addDown (E.q i) (mulVecDown E.Q w i))
  Ellipsoid.isPsd E.Q && le (E.quadUp w) one &&
    (List.finRange n).all fun i => le (E.I_error.inf i) (lo i) && le (hi i) (E.I_error.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
