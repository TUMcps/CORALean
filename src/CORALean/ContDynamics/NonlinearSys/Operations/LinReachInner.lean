import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachInnerState
import CORALean.ContDynamics.NonlinearSys.Operations.LinReachInnerErr
import CORALean.ContSet.ContSet.ContSet
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# `linReachInner`, CORA's inner linearized step

CORA's `contDynamics/linReachInner.m`, the step of `'minkdiff'` `reachInner` and its form of a
step of [1, Alg. 1], line by line over exact sets, the representation-specific calls supplied
(`LinReachInnerOps`): `some none` when the start box is empty (`options.empty`), `none` when
the error loop (`linReachInnerErr`) runs out of `fuel`. Two departures, both where CORA is
unsound: `minkDiff` is the exact `minkowskiDiff`, not CORA's default `'approx'`
(`Zonotope.minkDiffApprox_not_inner`); and `Rti` is `Rinit ∪ Rtp`, each inside the reachable
set at its own time, not CORA's `convHull_(Rstart_ti_cZ, Rend_ti_cZ)`, [1, Prop. 2], which is
not inner (`convexHull_timeInterval_convex_counterexample`), so `Rstart_ti` and `Rend_ti` are
not computed.

## References

* [1] M. Wetzlinger, A. Kulmburg and M. Althoff. "Inner Approximations of Reachable Sets for
  Nonlinear Systems using the Minkowski Difference". IEEE Control Systems Letters,
  8:2033-2038, 2024.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝓛 : Type}


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
  (NonlinearSys.linReachInnerErr ops Δt A p Rlinti__ abstrerr fuel).map fun r =>  -- while loop
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
