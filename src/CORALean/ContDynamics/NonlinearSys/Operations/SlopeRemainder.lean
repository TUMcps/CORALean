module

public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatModel
public import CORALean.ContSet.Interval.Float.Operations.MatPlus
public import CORALean.ContSet.Interval.Float.Operations.MtimesIntervalMat
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# The abstraction error from a slope enclosure

The box `L` an `AbstractionError` certificate asks for, computed in `𝕋` from the model's slope
boxes over `X × U`: what is left once the affine part at `(x✱, u✱)` is taken off lies in
`L = ([J_x] - A)(X - x✱) ⊕ ([J_u] - B)(U - u✱)`. A departure from CORA's `'lin'`
(`priv_abstrerr_lin`), which bounds the remainder by the second-order Lagrange term from an
interval Hessian [1, Prop. 1]: `FloatModel` carries no Hessian enclosure, so this is the
first-order mean-value remainder, coarser, `O(‖δ‖)` where the Hessian's is `O(‖δ‖²)`.
`FloatHessModel.hessRemainder` is the float Hessian run.

## Inputs
* `fm` – float model
* `A` – state Jacobian center
* `B` – input Jacobian center
* `xs` – state expansion point
* `us` – input expansion point
* `X` – state box
* `U` – input box

## Output
* the box enclosing the linearization remainder

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear
      Systems with Uncertain Parameters using Conservative Linearization". In
      Proc. of the 47th IEEE Conference on Decision and Control (CDC), 2008,
      pp. 4042-4048.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `([J_x] - A)(X - xs) ⊕ ([J_u] - B)(U - us)`, the slope boxes taken over
`X × U`. -/
def NonlinearSys.FloatModel.slopeRemainder (fm : NonlinearSys.FloatModel 𝕋 n m)
    (A : Mat 𝕋 n n) (B : Mat 𝕋 n m) (xs : Vec 𝕋 n) (us : Vec 𝕋 m) (X : Interval (Vec 𝕋 n))
    (U : Interval (Vec 𝕋 m)) : Interval (Vec 𝕋 n) :=
  let ΔJx := Interval.matPlus (fm.jacX X U) (Interval.point (-A))  -- [J_x] - A
  let ΔJu := Interval.matPlus (fm.jacU X U) (Interval.point (-B))  -- [J_u] - B
  let dx := Interval.plus X (Interval.point (-xs))                     -- X - x✱
  let du := Interval.plus U (Interval.point (-us))                     -- U - u✱
  Interval.plus (Interval.mtimesIntervalMat ΔJx dx) (Interval.mtimesIntervalMat ΔJu du)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
