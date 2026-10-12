import CORALean.ContSet.HPolytope.Float.HPolytope
import CORALean.ContSet.Interval.Float.Operations.MulLo

/-!
# `HPolytope.scaleDevLo`, the lower end of what rounding a scaled row costs over a domain

A row `v` scaled by `s` is stored as `ṽ = s v` rounded down. Each entry of the exact scaled row
`s v` lies between its two roundings, so its deviation from the stored entry is between the
roundings less the stored entry, rounded outward. Over a box `dom` the deviation `(s v - ṽ)ᵀ x` is
then at least this sum of lower corner products, each rounded down.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]  {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The lower bound of `(s v - ṽ)ᵀ x` over `x ∈ dom`, for `ṽ = mulDown v s`. -/
def HPolytope.scaleDevLo (v : Vec 𝕋 n) (s : 𝕋) (dom : Interval (Vec 𝕋 n)) : 𝕋 :=
  sumDown fun j =>
    Interval.mulLo (subDown (mulDown (v j) s) (mulDown (v j) s))
      (subUp (mulUp (v j) s) (mulDown (v j) s)) (dom.inf j) (dom.sup j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
