module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripLiu

@[expose] public section

/-!
# `LinearSysDT.observeEsoB`

CORA's ellipsoidal observer `ESO-B` (`priv_observe_ESO_B`) for one step, corrected so that it
encloses the true state (`LinearSysDT.observeEsoB_outer`), on `E(Q, c)` at the level `1`. The step
is `post` (shape `A Q Aᵀ`, center `A c + B u + c_sys`), the prediction
`Q_next = (1 - p)⁻¹ A Q Aᵀ + p⁻¹ W` at any `p ∈ (0, 1)` where the code has `(σ² p)⁻¹ W` (Eq. 21 of
Liu, Zhao and Wu, IET Control Theory & Applications, 2016), then, when the trigger
`σ²_prev + δᵀδ > 1` fires, the corrected update `Ellipsoid.intersectStripLiu` (Thm. 3) at the
level `1` of the predicted set, where the code passes its `sigma_sq`, otherwise the prediction
unchanged. `LinearSysDT.observeEsoB1D` is the step as the code computes it, with its counterexample.

## Inputs
* `sys` – system
* `W` – disturbance shape
* `V` – noise shape
* `p` – prediction weight
* `lam` – update weight
* `σsqPrev` – previous sigma squared
* `u` – input at this step
* `y` – measurement
* `Q` – ellipsoid shape
* `c` – ellipsoid center

## Output
* the updated ellipsoid
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def LinearSysDT.observeEsoB (sys : LinearSysDT ℝ n)
    (W : Mat ℝ n n) (V : Mat ℝ sys.q sys.q) (p lam σsqPrev : ℝ) (u : Vec ℝ sys.m)
    (y : Vec ℝ sys.q)
    (Q : Mat ℝ n n) (c : Vec ℝ n) : Ellipsoid n :=
  let Qhom := sys.A * Q * sys.Aᵀ  -- `Rnext_hom = post(...)`: the shape of `A*Rnext.tp`
  let chom := sys.A *ᵥ c + (sys.B *ᵥ u + sys.c)  -- its center, `A c + B u + c`
  let Qnext := (1 - p)⁻¹ • Qhom + p⁻¹ • W  -- `Q_next`; the code has `(sigma_sq*p)^-1`
  let δ := y - sys.C *ᵥ chom  -- `delta` of `aux_methodLiu2016`
  if σsqPrev + δ ⬝ᵥ δ > 1 then  -- Theorem 3 of Liu et al.
    Ellipsoid.intersectStripLiu Qnext chom sys.C V y 1 lam  -- corrected; the code passes `sigma_sq`
  else Ellipsoid.ofShape Qnext chom  -- the ellipsoid is unchanged

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
