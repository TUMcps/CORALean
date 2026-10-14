module

public import CORALean.ContDynamics.NonlinearSys.Operations.AbstrErrLoop
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Lattice
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `linReachCora1D`, CORA's `'lin'` step in one dimension at a vanishing Jacobian

CORA's `@contDynamics/linReach.m` at `alg = 'lin'`, `tensorOrder = 2`, default `maxError = Inf`,
without inputs, line by line: `linearize` (`p = cx + f(cx)·Δt/2`), `oneStep` from `Rdelta`, the
`while perfIndCurr > 1` loop over `priv_abstrerr_lin` ([1, Prop. 1], its Hessian read over
`interval(Rmax) + p`), and `Rerror`. Sets are `Real.Interval ℝ`: in 1D a zonotope is its
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

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `'lin'` step for `ẋ = f(x)` from `Rinit`, Jacobian `f'`, Hessian bound `hess`:
`(Rti, Rtp)` as intervals, or `none` when `f'(p) ≠ 0` or `fuel` passes have not
settled. -/
noncomputable def NonlinearSys.linReachCora1D (f f' : ℝ → ℝ) (hess : ℝ → ℝ → ℝ)
    (Rinit : Real.Interval ℝ) (Δt : ℝ) (fuel : ℕ) :
    Option (Real.Interval ℝ × Real.Interval ℝ) :=
  -- linearize
  let cx := (Rinit.inf + Rinit.sup) / 2                       -- cx = center(R)
  let f0prev := f cx                                      -- f0prev = nlnsys.mFile(cx,p.u)
  let p := cx + f0prev * (1 / 2) * Δt                     -- p.x = cx + f0prev*0.5*timeStep
  let f0 := f p                                           -- f0 = nlnsys.mFile(p.x,p.u)
  let A := f' p                                           -- [A,B] = nlnsys.jacobian(p.x,p.u)
  if A ≠ 0 then none else
  let Rdelta : Real.Interval ℝ := ⟨Rinit.inf - p, Rinit.sup - p⟩          -- Rdelta = Rinit + (-p.x)
  -- oneStep at `A = 0`
  let Pu := Δt * f0                                       -- particularSolution_constant
  let Htp : Real.Interval ℝ := ⟨Rdelta.inf + Pu, Rdelta.sup + Pu⟩           -- Htp = eAdt*X + Pu
  -- Hti = enclose(X,Htp) + C_state
  let Hti : Real.Interval ℝ := ⟨min Rdelta.inf Htp.inf, max Rdelta.sup Htp.sup⟩
  let Rtp := Htp                                          -- Rtp = Htp + PU
  let Rti := Hti                                          -- Rti = Hti + PU + C_input
  -- the true error induced by an applied one
  let Φ : ℝ → ℝ := fun appliedError =>
    let RallError := Δt * appliedError                    -- particularSolution_timeVarying
    -- Rmax = Rti + RallError
    let Rmax : Real.Interval ℝ := ⟨Rti.inf - RallError, Rti.sup + RallError⟩
    let totalInt : Real.Interval ℝ := ⟨Rmax.inf + p, Rmax.sup + p⟩         -- totalInt_x = IHx + p.x
    let H := hess totalInt.inf totalInt.sup                   -- H_ = max(inf(abs(H)),sup(abs(H)))
    let dx := max |Rmax.inf| |Rmax.sup|                     -- dx = max(abs(inf(IHx)),abs(sup(IHx)))
    1 / 2 * dx * H * dx                                   -- errorLagr = 0.5*dz'*H_*dz
  -- while perfIndCurr > 1: appliedError = 1.1*abstrerr, from abstrerr = 0
  match abstrErrLoop (S := fun _ => ℝ) (n := 1) (fun te ae => decide (te ≤ ae))
      (fun e => 11 / 10 * e) Φ 0 fuel with
  | none => none
  | some trueError =>
    let Rerror := Δt * trueError                          -- particularSolution_timeVarying
    some (⟨Rti.inf + p - Rerror, Rti.sup + p + Rerror⟩,       -- Rti = Rti + p.x + Rerror
      ⟨Rtp.inf + p - Rerror, Rtp.sup + p + Rerror⟩)           -- Rtp = Rtp + p.x + Rerror

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
