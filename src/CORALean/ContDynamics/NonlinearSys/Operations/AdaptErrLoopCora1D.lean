import Mathlib.Data.Real.Basic

/-!
# `adaptErrLoopCora1D`, the abstraction-error loop of CORA's `linReach_adaptive`

The inner `while true` loop of CORA's `@nonlinearSys/linReach_adaptive.m` at `alg = 'lin'`, in
one dimension: from an admissible error `error_adm`, compute the `trueError` it induces
(`Φ`, which the caller builds from `RallError`, `Rmax` and `priv_abstractionError_adaptive`),
accept it once it fits, else enlarge `error_adm` to `1.1 * trueError` and repeat; from the third
pass on, a `perfIndCurr` above the previous one gives up (`options.Lconverged = false`, `none`).

Over the reals with `trueError ≥ 0` and `error_adm ≥ 0`, `perfIndCurr <= 1 || ~any(trueError)`
is `trueError ≤ error_adm` (`trueError / 0` is `Inf` for a positive `trueError`, and a zero one
is `~any`). `perfIndCounter` starts at `1`; `perfInds(1)` is never compared. The loop states no
iteration count, so `fuel` bounds it and running out is `none`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's abstraction-error loop of `linReach_adaptive` in 1D: the accepted `trueError`, or
`none` when it gives up or `fuel` passes have not settled. -/
noncomputable def NonlinearSys.adaptErrLoopCora1D (Φ : ℝ → ℝ) :
    ℕ → ℕ → ℝ → ℝ → Option ℝ
  | 0, _, _, _ => none
  | fuel + 1, perfIndCounter, error_adm, perfIndPrev =>
    let trueError := Φ error_adm                          -- [..,trueError,..] = priv_abstr...(Rmax)
    let perfIndCurr := trueError / error_adm              -- perfIndCurr = max(trueError./error_adm)
    if trueError ≤ error_adm then some trueError          -- if perfIndCurr <= 1 || ~any(trueError)
    else if 2 < perfIndCounter ∧ perfIndPrev < perfIndCurr then none -- Lconverged = false
    else NonlinearSys.adaptErrLoopCora1D Φ fuel (perfIndCounter + 1) -- perfIndCounter + 1
      (11 / 10 * trueError) perfIndCurr                   -- error_adm = 1.1 * trueError

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
