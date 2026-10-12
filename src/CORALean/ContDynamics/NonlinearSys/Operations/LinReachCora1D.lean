import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice

/-!
# `linReachCora1D`, CORA's `'lin'` step in one dimension at a vanishing Jacobian

CORA's `@contDynamics/linReach.m` at `alg = 'lin'`, `tensorOrder = 2`, default `maxError = Inf`,
without inputs, line by line: `linearize` (`p = cx + f(cx)·Δt/2`), `oneStep` from `Rdelta`, the
`while perfIndCurr > 1` loop over `priv_abstrerr_lin` ([1, Prop. 1], its Hessian read over
`interval(Rmax) + p`), and `Rerror`. Sets are intervals as `(inf, sup)`: in 1D a zonotope is its
interval hull, and `enclose(X, X + v)` is `conv(X ∪ (X + v))`. Only `A = f'(p) = 0` is modelled
(else `none`): there `eAdt = 1`, `E = F = G = 0`, `particularSolution_constant` is `Δt · uTrans`
(`Ainv` is empty) and `particularSolution_timeVarying` of a box `V` is `Δt · V`; `PU = 0`, `du = 0`.

`hess lo hi` is CORA's `max(infimum(abs(H)), supremum(abs(H)))` for its interval Hessian over
`totalInt_x = [lo, hi]`, supplied as the user's Hessian file supplies it. At `maxError = Inf`,
`perfInd` is zero, so the loop is `abstrErrLoop` with factor `1.1` and test `perfIndCurr ≤ 1`,
over the reals `trueError ≤ appliedError` (`0/0`, `NaN`, also ends MATLAB's loop); it states no
iteration count, so `fuel` is an argument and the result an `Option`.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear Systems with
      Uncertain Parameters using Conservative Linearization". In Proc. of the 47th IEEE
      Conference on Decision and Control (CDC), 2008, pp. 4042-4048.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `'lin'` step for `ẋ = f(x)` from `Rinit`, Jacobian `f'`, Hessian bound `hess`:
`(Rti, Rtp)` as `(inf, sup)` pairs, or `none` when `f'(p) ≠ 0` or `fuel` passes have not
settled. -/
noncomputable def NonlinearSys.linReachCora1D (f f' : ℝ → ℝ) (hess : ℝ → ℝ → ℝ)
    (Rinit : ℝ × ℝ) (Δt : ℝ) (fuel : ℕ) : Option ((ℝ × ℝ) × (ℝ × ℝ)) :=
  -- linearize
  let cx := (Rinit.1 + Rinit.2) / 2                       -- cx = center(R)
  let f0prev := f cx                                      -- f0prev = nlnsys.mFile(cx,p.u)
  let p := cx + f0prev * (1 / 2) * Δt                     -- p.x = cx + f0prev*0.5*timeStep
  let f0 := f p                                           -- f0 = nlnsys.mFile(p.x,p.u)
  let A := f' p                                           -- [A,B] = nlnsys.jacobian(p.x,p.u)
  if A ≠ 0 then none else
  let Rdelta := (Rinit.1 - p, Rinit.2 - p)                -- Rdelta = Rinit + (-p.x)
  -- oneStep at `A = 0`
  let Pu := Δt * f0                                       -- particularSolution_constant
  let Htp := (Rdelta.1 + Pu, Rdelta.2 + Pu)               -- Htp = eAdt*X + Pu
  let Hti := (min Rdelta.1 Htp.1, max Rdelta.2 Htp.2)     -- Hti = enclose(X,Htp) + C_state
  let Rtp := Htp                                          -- Rtp = Htp + PU
  let Rti := Hti                                          -- Rti = Hti + PU + C_input
  -- the true error induced by an applied one
  let Φ : ℝ → ℝ := fun appliedError =>
    let RallError := Δt * appliedError                    -- particularSolution_timeVarying
    let Rmax := (Rti.1 - RallError, Rti.2 + RallError)    -- Rmax = Rti + RallError
    let totalInt := (Rmax.1 + p, Rmax.2 + p)              -- totalInt_x = IHx + p.x
    let H := hess totalInt.1 totalInt.2                   -- H_ = max(inf(abs(H)),sup(abs(H)))
    let dx := max |Rmax.1| |Rmax.2|                       -- dx = max(abs(inf(IHx)),abs(sup(IHx)))
    1 / 2 * dx * H * dx                                   -- errorLagr = 0.5*dz'*H_*dz
  -- while perfIndCurr > 1: appliedError = 1.1*abstrerr, from abstrerr = 0
  match abstrErrLoop (S := fun _ => ℝ) (n := 1) (fun te ae => decide (te ≤ ae))
      (fun e => 11 / 10 * e) Φ 0 fuel with
  | none => none
  | some trueError =>
    let Rerror := Δt * trueError                          -- particularSolution_timeVarying
    some ((Rti.1 + p - Rerror, Rti.2 + p + Rerror),       -- Rti = Rti + p.x + Rerror
      (Rtp.1 + p - Rerror, Rtp.2 + p + Rerror))           -- Rtp = Rtp + p.x + Rerror

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
