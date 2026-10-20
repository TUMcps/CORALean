module

public import CORALean.ContDynamics.NonlinearSys.Operations.LinReachFloat
public import CORALean.ContDynamics.NonlinearSys.Operations.RelinStepFloat

@[expose] public section

/-!
# One step at abstraction order `κ`, in floats

[1, Alg. 2] weighs two abstraction orders, `κ = 1` and `κ = 2`, whose errors eqs. (46)-(47)
compare. In `𝕋` the first is `relinStepFloat`, whose abstraction error is the slope remainder of
the model's Jacobian boxes, first order in the deviation from the expansion point; the second is
`linReachFloat` at `'lin'`, whose error is the Hessian remainder of a `FloatHessModel`, second
order. Either way the region is checked first, so the abstraction-error loop of lines 7-11 needs
no fixed point. Any `κ` other than `1` is the second order.

## Inputs
* `fm` – float Hessian model
* `κ` – abstraction order
* `U` – input zonotope
* `options` – reachability options
* `R` – start zonotope

## Output
* the time-interval and end sets, or none

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `(R(τ_k), R(t_{k+1}))` from `R` under inputs in `U` at abstraction order `κ`, or `none`
if the region check or the linear step fails. -/
def NonlinearSys.FloatHessModel.orderStepFloat [SoundFloatArithmetic 𝕋] [ToRat 𝕋]
    (fm : NonlinearSys.FloatHessModel 𝕋 n m) (κ : ℕ) (U : Zonotope (Vec 𝕋 m))
    (options : LinearSys.ReachOptions 𝕋) (R : Zonotope (Vec 𝕋 n)) :
    Option (Zonotope (Vec 𝕋 n) × Zonotope (Vec 𝕋 n)) :=
  if κ = 1 then fm.toFloatModel.relinStepFloat U options R          -- 7. abstrErr, κ = 1
  else fm.linReachFloat .lin U options R                            -- 7. abstrErr, κ = 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
