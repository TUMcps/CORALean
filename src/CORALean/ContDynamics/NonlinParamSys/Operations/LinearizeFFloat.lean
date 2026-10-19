module

public import CORALean.ContDynamics.NonlinParamSys.Definitions.FloatModel
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `NonlinParamSys.FloatModel.linearizeFFloat`

The constant term of CORA's `nonlinParamSys/linearize` [1], the `paramInt` branch, in `𝕋`, as
`NonlinParamSys.linearizeF` is over ℝ: the model's enclosure of `f(p.x, p.u, p)` over the
parameter box, at the point boxes of the expansion point. It holds at every parameter of the box
(`linearizeFloat_f_mem`), and `linearizeFloat` hands its center on as the constant of the system
it returns. Where CORA splits `f` along the unit vectors and so assumes it affine in `p`, the
model's enclosure over `P` asks no such thing.

## References

* [1] `contDynamics/@nonlinParamSys/linearize.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The enclosure of the constant term `f(xs, us, p)` over the parameter box `P`. -/
def NonlinParamSys.FloatModel.linearizeFFloat (fm : NonlinParamSys.FloatModel 𝕋 n m q)
    (xs : Vec 𝕋 n) (us : Vec 𝕋 m) (P : Interval (Vec 𝕋 q)) : Interval (Vec 𝕋 n) :=
  fm.f (Interval.point xs) (Interval.point us) P                    -- [f(p.x, p.u, p)]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
