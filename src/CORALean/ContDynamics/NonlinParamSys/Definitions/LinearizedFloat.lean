import CORALean.ContDynamics.NonlinParamSys.Definitions.FloatModel

/-!
# What the float `nonlinParamSys/linearize` hands on

`NonlinParamSys.Linearized` in `𝕋`: the point `(p.x, p.u)` it expands about, the centre `p.p`
of the parameter box, and in place of the zonotopes `zf`, `zA`, `zB` the interval enclosures of
the constant term and of the two Jacobians over the box.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} {n m q : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure NonlinParamSys.LinearizedFloat (𝕋 : Type) (n m q : ℕ) where
  xs : Vec 𝕋 n
  us : Vec 𝕋 m
  ps : Vec 𝕋 q
  f : Interval (Vec 𝕋 n)
  A : Interval (Mat 𝕋 n n)
  B : Interval (Mat 𝕋 n m)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
