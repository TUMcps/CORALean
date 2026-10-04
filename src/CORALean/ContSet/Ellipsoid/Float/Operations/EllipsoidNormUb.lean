import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
import CORALean.Global.Float.Sqrt
import CORALean.Global.Float.ToRat

/-!
# `Ellipsoid.ellipsoidNormUb`, over a floating-point scalar

An upper bound on CORA's `@ellipsoid/ellipsoidNorm` (full-rank branch, `sqrt(pᵀ Q⁻¹ p)`), whose
solve `Q \ p` no rounded arithmetic does exactly. The caller proposes generator coefficients `u`
with `G u = p`, checked exactly in ℚ (`ToRat`); then `p` lies on the boundary of the ellipsoid
scaled by `‖u‖₂`, so its ellipsoid norm is at most that length, rounded up (`normUp`). `none`
when the equation fails. Of the nominal ellipsoid, as CORA's (the shape matrix alone); not the
norm itself, which is the least such length.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps ToRat

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `prec` is the precision of the upward square root. -/
def Ellipsoid.ellipsoidNormUb (prec : ℕ) (E : Ellipsoid 𝕋 n) (p : Vec 𝕋 n) (u : Vec 𝕋 E.k) :
    Option 𝕋 :=
  let image : Vec ℚ n := fun i => ∑ j, toRat (E.G i j) * toRat (u j)
  let solves : Bool := (List.finRange n).all fun i => decide (image i = toRat (p i))
  if solves then some (normUp prec u) else none

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
