import CORALean.ContDynamics.NonlinearSys.Definitions.LinReachInnerOps
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# `linReachInnerErr`, the abstraction error loop of CORA's inner linearized step

The `while perfIndCurr > 1` loop of CORA's `contDynamics/linReachInner.m`, its form of lines
10-13 of [1, Alg. 1]: enlarge the error guess `abstrerr` by `1.1`, take the reachable set of its
box `zonotope(0, diag(·))` under the linearized dynamics (`particularSolution_timeVarying`),
boxed, add it to the time-interval box `Rlinti__` of the linearized dynamics, compute the true
error on that region (`priv_abstrerr_lin`), and repeat until the true error lies below the
applied one componentwise: `perfIndCurr = max(trueError ./ appliedError) ≤ 1`, which over the
reals reads `trueError ≤ appliedError` in every component (a component with `0/0`, `NaN`, is
skipped by `max`, and `0 ≤ 0` holds). The result is the last `trueError`, `VerrorDyn` and the
region `Rmax__`, all of which the step spends.

`perfIndCurr = Inf` starts the loop, so it runs at least once; the loop states no iteration
count, so `fuel` is an argument and the result an `Option`, `none` once `fuel` passes have not
met the condition.

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

open Pointwise

variable {n : ℕ} {𝓛 : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The loop `while perfIndCurr > 1` of CORA's `linReachInner` from the guess `abstrerr`, for
the linearization `A` at `p` and the box `Rlinti__`: `(trueError, VerrorDyn, Rmax__)`, or `none`
once `fuel` passes have not settled. -/
noncomputable def NonlinearSys.linReachInnerErr (ops : NonlinearSys.LinReachInnerOps n 𝓛)
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
    else NonlinearSys.linReachInnerErr ops Δt A p Rlinti__ trueError k  -- abstrerr = trueError

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
