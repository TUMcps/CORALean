import CORALean.ContDynamics.NonlinParamSys.Definitions.LinearizedFloat
import CORALean.ContSet.Interval.Float.Operations.Center
import CORALean.ContSet.Interval.Float.Operations.Point

/-!
# `NonlinParamSys.FloatModel.linearizeFloat`

CORA's `nonlinParamSys/linearize` [1], the `paramInt` branch, in `𝕋`. The model is evaluated at
the point boxes of the expansion point `(xs, us)` over the parameter box `P`: the enclosure of
the constant term and of the two Jacobians, each holding at every parameter of the box
(`linearizeFloat_f_mem` and its two siblings). Where CORA splits `f` along the unit vectors and
so assumes it affine in `p`, the model's enclosure over `P` asks no such thing. The centre of the
box is the stored `Interval.center`, rounded up. The `'linRem'` option and the numeric-`p`
branch are not carried.

## References

* [1] `contDynamics/@nonlinParamSys/linearize.m`
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def NonlinParamSys.FloatModel.linearizeFloat (fm : NonlinParamSys.FloatModel 𝕋 n m q)
    (xs : Vec 𝕋 n) (us : Vec 𝕋 m) (P : Interval (Vec 𝕋 q)) :
    NonlinParamSys.LinearizedFloat 𝕋 n m q :=
  let X := Interval.point xs                                        -- the point box of p.x
  let U := Interval.point us                                        -- the point box of p.u
  { xs := xs, us := us, ps := P.center                              -- p.x, p.u, p.p
    f := fm.f X U P                                                 -- [f(p.x, p.u, p)]
    A := fm.jacX X U P                                              -- [∂f/∂x (p.x, p.u, p)]
    B := fm.jacU X U P }                                            -- [∂f/∂u (p.x, p.u, p)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
