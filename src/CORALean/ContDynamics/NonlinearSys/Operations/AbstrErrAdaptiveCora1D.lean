import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice

/-!
# `abstrErrAdaptiveCora1D`, CORA's `priv_abstractionError_adaptive` in one dimension

CORA's `@nonlinearSys/private/priv_abstractionError_adaptive.m` at `alg = 'lin'`,
`tensorOrder = 2`, without inputs (`U = 0`, so `du = 0`), line by line: the box of `R = Rmax`,
shifted by the linearization point `p` to `totalInt_x`, its largest magnitude `dx`, and the
Lagrange term `0.5 * dz' * H_ * dz` of [1, Prop. 1] with the Hessian read over `totalInt_x`.

Intervals are `(inf, sup)` pairs. `hessIv lo hi` is CORA's interval Hessian `H` over
`[lo, hi]`, as the user's Hessian file evaluates it; `max(infimum(abs(H)), supremum(abs(H)))` is
`max |inf H| |sup H|`. `hessianConst` is `options.hessianConst` once `options.isHessianConst`
holds (`some`), else `none`; the check that sets it runs in the caller.

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

/-- CORA's `priv_abstractionError_adaptive` (`'lin'`, `tensorOrder = 2`) in 1D without inputs:
`trueError` for the box `Rmax`, linearization point `p`, interval Hessian `hessIv`. -/
noncomputable def NonlinearSys.abstrErrAdaptiveCora1D (hessIv : ℝ → ℝ → ℝ × ℝ)
    (hessianConst : Option ℝ) (p : ℝ) (Rmax : ℝ × ℝ) : ℝ :=
  let IH_x := Rmax                                        -- IH_x = interval(R)
  let totalInt_x := (IH_x.1 + p, IH_x.2 + p)              -- totalInt_x = IH_x + p.x
  let IHinf := |IH_x.1|                                   -- IHinf = abs(infimum(IH_x))
  let IHsup := |IH_x.2|                                   -- IHsup = abs(supremum(IH_x))
  let dx := max IHinf IHsup                               -- dx = max(IHinf,IHsup)
  match hessianConst with
  | none =>                                               -- if ~options.isHessianConst
    let H := hessIv totalInt_x.1 totalInt_x.2             -- H = nlnsys.hessian(totalInt_x,...)
    let H_ := max |H.1| |H.2|                             -- H_ = max(infimum(H_),supremum(H_))
    1 / 2 * dx * H_ * dx                                  -- err(i,1) = 0.5 * dz' * H_ * dz
  | some H_ =>                                            -- use saved H_
    1 / 2 * dx * H_ * dx                                  -- err(i,1) = 0.5*dz'*hessianConst*dz

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
