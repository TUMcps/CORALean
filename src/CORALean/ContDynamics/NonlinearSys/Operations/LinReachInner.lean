module

public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachInnerOps
public import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachInnerState
public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import CORALean.Global.StepOf

@[expose] public section

/-!
# `linReachInner`, CORA's inner linearized step

CORA's `contDynamics/linReachInner.m`, the step of `'minkdiff'` `reachInner` and its form of a
step of [1, Alg. 1], over exact sets with the representation-specific calls supplied
(`LinReachInnerOps`): `some none` when the start box is empty, `none` when the error loop
runs out of `fuel`. Two departures, where CORA is unsound: `minkDiff` is the exact
`minkowskiDiff`, not CORA's `'approx'` (`Zonotope.minkDiffApprox_not_inner`); and `Rti` is
`Rinit ∪ Rtp`, not CORA's `convHull_(Rstart_ti_cZ, Rend_ti_cZ)` [1, Prop. 2], which is not
inner (`convexHull_timeInterval_convex_counterexample`).

## Inputs
* `ops` – set operations
* `f` – autonomous field
* `Δt` – step size
* `fuel` – bound for error loop
* `Rinit` – start set
* `abstrerr` – abstraction error guess

## Output
* the inner step state, or none

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
      Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
      2024.](../../../../../references/2024/wetzlinger-lcss-inner-minkowski-difference.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝓛 : Type}
open Pointwise


-- ------------------------------------------  STEPS  ------------------------------------------- --

/-- The loop `while perfIndCurr > 1` of CORA's `linReachInner` from the guess `abstrerr`, for
the linearization `A` at `p` and the box `Rlinti__`: `(trueError, VerrorDyn, Rmax__)`, or `none`
once `fuel` passes have not settled. -/
@[step_of NonlinearSys.linReachInner]
noncomputable def NonlinearSys.step_linReachInnerErr (ops : NonlinearSys.LinReachInnerOps n 𝓛)
    (Δt : ℝ) (A : Mat ℝ n n) (p : Vec ℝ n) (Rlinti__ : Set (Vec ℝ n)) :
    Vec ℝ n → ℕ → Option (Vec ℝ n × 𝓛 × Set (Vec ℝ n))
  | _, 0 => none
  | abstrerr, k + 1 =>
    let appliedError := (11 / 10 : ℝ) • abstrerr                -- appliedError = 1.1*abstrerr
    let Verror := ops.diagZono appliedError                     -- Verror = zonotope(0, diag(·))
    let RallError := ops.box (ops.inputSol Δt A Verror)         -- RallError = interval(...)
    let Rmax__ := Rlinti__ + RallError                          -- Rmax__ = Rlinti__ + RallError
    let trueError := (ops.abstrErr p Rmax__).1                  -- [trueError,VerrorDyn] =
    let VerrorDyn := (ops.abstrErr p Rmax__).2                  --   priv_abstrerr_lin(...)
    if ∀ i, trueError i ≤ appliedError i then                   -- while perfIndCurr > 1
      some (trueError, VerrorDyn, Rmax__)
    else NonlinearSys.step_linReachInnerErr ops Δt A p Rlinti__ trueError k  -- abstrerr = trueError


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `linReachInner` from the start set `Rinit` and the error guess `abstrerr`, for the
field `f` and the step `Δt`: `some none` when the start box is empty, `none` once the error
loop has run `fuel` passes. -/
noncomputable def NonlinearSys.linReachInner (ops : NonlinearSys.LinReachInnerOps n 𝓛)
    (f : Vec ℝ n → Vec ℝ n) (Δt : ℝ) (fuel : ℕ) (Rinit : Set (Vec ℝ n)) (abstrerr : Vec ℝ n) :
    Option (Option (NonlinearSys.LinReachInnerState n 𝓛)) :=
  let Rinit_interval := ops.box Rinit                           -- Rinit_interval = interval(Rinit)
  let c_Rinit_interval := ops.cen Rinit_interval                -- center(Rinit_interval)
  if ops.isEmpty Rinit_interval then some none else             -- options.empty = true
  let p := c_Rinit_interval + (Δt / 2) • f c_Rinit_interval     -- linearizationPoint
  let A := ops.jac p                                            -- linearize
  let u := f p                                                  -- u = center(linOptions.uTrans)
  let Rinit__ := (fun x => x - p) '' Rinit                      -- Rinit__ = Rinit + (-p)
  let Rcon := ∫ θ in (0:ℝ)..Δt, exp ((Δt - θ) • A) *ᵥ u          -- particularSolution_constant
  let eADeltat := exp (Δt • A)                                  -- getTaylor(linsys,'eAdt',...)
  let Rlintp__ := (fun x => eADeltat *ᵥ x + Rcon) '' Rinit__    -- Rlintp__ = eADeltat*Rinit__+Rcon
  let Rstart_interval__ := (fun x => x - p) '' Rinit_interval   -- Rinit_interval + (-p)
  let C := ops.curv Δt A Rstart_interval__ u                    -- C = F*zonotope(.) + G*u
  let Rlintp_outerapprox__ := (fun x => eADeltat *ᵥ x + Rcon) '' Rstart_interval__
  let Rlinti__ := convexHull ℝ (Rstart_interval__ ∪ (Rlintp_outerapprox__ + ops.box C))
  (NonlinearSys.step_linReachInnerErr ops Δt A p Rlinti__ abstrerr fuel).map fun r =>  -- while loop
    let abstrerr' := r.1                                        -- abstrerr = trueError
    let VerrorDyn := r.2.1
    let Rmax__ := r.2.2
    let Rerror := ops.inputSol Δt A VerrorDyn                   -- particularSolution_timeVarying
    let Rlintp := (fun x => x + p) '' Rlintp__                  -- Rlintp__ + p
    let Rtp := minkowskiDiff Rlintp Rerror                      -- Rtp.set = minkDiff(., Rerror)
    let Rmax := (fun x => x + p) '' Rmax__                      -- Rmax = Rmax__ + p
    let Rti := Rinit ∪ Rtp                                      -- Rti: replaces CORA's Prop. 2
    some { p, A, u, C, Rcon, Rlintp, Rmax, err := abstrerr', VerrorDyn, Rerror, Rtp, Rti }

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
