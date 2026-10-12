import CORALean.ContSet.HPolytope.Float.HPolytope
import CORALean.ContSet.Interval.Float.Operations.MulHi

/-!
# `HPolytope.scaleDevHi`, the upper end of what rounding a scaled row costs over a domain

The upper counterpart of `scaleDevLo`: the sum of the upper corner products, each rounded up.
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

/-- The upper bound of `(s v - ṽ)ᵀ x` over `x ∈ dom`, for `ṽ = mulDown v s`. -/
def HPolytope.scaleDevHi (v : Vec 𝕋 n) (s : 𝕋) (dom : Interval (Vec 𝕋 n)) : 𝕋 :=
  sumUp fun j =>
    Interval.mulHi (subDown (mulDown (v j) s) (mulDown (v j) s))
      (subUp (mulUp (v j) s) (mulDown (v j) s)) (dom.inf j) (dom.sup j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
