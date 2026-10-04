import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
import CORALean.Global.Float.EuclideanNorm

/-!
# `Ellipsoid.containsPoint`, over a floating-point scalar

CORA's `@ellipsoid/contains_` for a point, as a check of a caller-proposed certificate: the
factor vector `u` with `p = q + G u + e`. CORA solves `Q \ (p - q)`; a float solve is not exact,
so the solve is the caller's and only its result is checked: `‖u‖₂ ≤ 1` by the upward square sum,
and the remainder `p - q - G u`, bracketed by directed roundings, inside the error box. Only
`true` is certain; `false` says only that this `u` does not show membership.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.containsPoint (E : Ellipsoid 𝕋 n) (p : Vec 𝕋 n) (u : Vec 𝕋 E.k) : Bool :=
  -- the remainder `p - q - G u`, between its two roundings
  let lo : Vec 𝕋 n := fun i => subDown (p i) (addUp (E.q i) (dotUp (fun j => E.G i j) u))
  let hi : Vec 𝕋 n := fun i => subUp (p i) (addDown (E.q i) (dotDown (fun j => E.G i j) u))
  le (sqSumUp fun j => absolute (u j)) one &&
    (List.finRange n).all fun i => le (E.err.inf i) (lo i) && le (hi i) (E.err.sup i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
