module

public import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripLiu1D

@[expose] public section

/-!
# `LinearSysDT.observeEsoB1D`

One step of CORA's ellipsoidal observer `ESO-B` (`priv_observe_ESO_B`) for `n = 1`, as the code
computes it: from the estimate `E(Q, c)` and the previous `σ²_prev`, the prediction of Eq. 21 and
Eq. 48 of Liu, Zhao and Wu (IET Control Theory & Applications, 2016),
`Q_next = (1 - p)⁻¹ A Q A + (σ²_prev p)⁻¹ W`, centered at `A c + u`, then the update of Thm. 3 of
the same paper (`intersectStrip(…, 'Liu2016')`): the trigger `σ²_prev + δ² > 1` and
`Ellipsoid.intersectStripLiu1D`; the observer starts from `R0` with `sigma_sq = 0.3`. The update's
shape is `(1 - λ)²` times the one the fusion needs (`Ellipsoid.intersectStripLiu1D_counterexample`,
`LinearSysDT.observeEsoB1D_counterexample`); `LinearSysDT.observeEsoB` is the corrected step.

## Inputs
* `A` – state coefficient
* `C` – output coefficient
* `W` – disturbance variance
* `V` – noise variance
* `u` – input at this step
* `y` – measurement
* `Q` – ellipsoid shape
* `c` – ellipsoid center
* `σsqPrev` – previous sigma squared

## Output
* the new center, shape and sigma squared
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def LinearSysDT.observeEsoB1D (A C W V u y Q c σsqPrev : ℝ) : ℝ × ℝ × ℝ :=
  let barV := Real.sqrt V⁻¹  -- `sys.bar_V = chol(inv(params.V.Q))`, eq. (51) of Liu et al.
  let auxRes := Real.sqrt W  -- `auxRes = sqrt(trace(params.W.Q))`
  let Qhom := A * Q * A  -- `Rnext_hom = post(...)`: the shape of `A*Rnext.tp`
  let chom := A * c + u  -- its center, `B u + c` folded into `u`
  let p := auxRes / (Real.sqrt (σsqPrev * Qhom) + auxRes)  -- `p`, eq. (48) of Liu et al.
  let Qnext := (1 - p)⁻¹ * Qhom + (σsqPrev * p)⁻¹ * W  -- `Q_next` (`1e-3`: a tolerance)
  let δ := y - C * chom  -- `delta` of `aux_methodLiu2016`
  if σsqPrev + δ * δ > 1 then  -- Theorem 3 of Liu et al.
    Ellipsoid.intersectStripLiu1D Qnext chom C V barV y σsqPrev  -- `E.c`, `E.Q`, `sigma_sq`
  else (chom, Qnext, σsqPrev)  -- the ellipsoid is unchanged

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
