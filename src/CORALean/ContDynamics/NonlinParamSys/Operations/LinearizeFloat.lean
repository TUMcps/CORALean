module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.NonlinParamSys.Definitions.FloatModel
public import CORALean.ContSet.Interval.Float.Operations.Center
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `NonlinParamSys.FloatModel.linearizeFloat`

CORA's `nonlinParamSys/linearize` [1], the `paramInt` branch, in `𝕋`, returning what the exact
`NonlinParamSys.linearize` returns: a `LinParamSys`, here over interval matrices, the set family
the float `LinParamSys.reachFloat` runs on, and the point `(p.x, p.u, p.p)`. The model is
evaluated at the point boxes of the expansion point `(xs, us)` over the parameter box `P`: the
enclosures of the two Jacobians are the system's `A` and `B` (`linearizeFloat_jacobianX_mem`,
`linearizeFloat_jacobianU_mem`), and the system's constant is the real value of the stored center
of the constant term's enclosure (`linearizeFloat_f_mem`). Where CORA splits `f` along the unit
vectors and so assumes it affine in `p`, the model's enclosure over `P` asks no such thing.

## Inputs
* `fm` – float model
* `xs` – state expansion point
* `us` – input expansion point
* `P` – parameter box

## Output
* the interval-matrix linearization with its expansion point

## References

* [1] `contDynamics/@nonlinParamSys/linearize.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m q : ℕ}


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The enclosure of the constant term `f(xs, us, p)` over the parameter box `P`. -/
@[step_of NonlinParamSys.FloatModel.linearizeFloat]
def NonlinParamSys.FloatModel.step_linearizeFFloat (fm : NonlinParamSys.FloatModel 𝕋 n m q)
    (xs : Vec 𝕋 n) (us : Vec 𝕋 m) (P : Interval (Vec 𝕋 q)) : Interval (Vec 𝕋 n) :=
  fm.f (Interval.point xs) (Interval.point us) P                    -- [f(p.x, p.u, p)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The linearization of the model about `(xs, us)` over the parameter box `P`: the system over
interval matrices, and `(p.x, p.u, p.p)`. -/
def NonlinParamSys.FloatModel.linearizeFloat (fm : NonlinParamSys.FloatModel 𝕋 n m q)
    (xs : Vec 𝕋 n) (us : Vec 𝕋 m) (P : Interval (Vec 𝕋 q)) :
    LinParamSys ℐ[𝕋] n × Vec 𝕋 n × Vec 𝕋 m × Vec 𝕋 q :=
  let X := Interval.point xs                                        -- the point box of p.x
  let U := Interval.point us                                        -- the point box of p.u
  let zf := fm.step_linearizeFFloat xs us P                              -- [f(p.x, p.u, p)]
  let A := fm.jacX X U P                                            -- [∂f/∂x (p.x, p.u, p)]
  let B := fm.jacU X U P                                            -- [∂f/∂u (p.x, p.u, p)]
  (⟨A, m, B, toRealVec zf.center⟩, xs, us, P.center)                -- linsys, p.x, p.u, p.p

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
