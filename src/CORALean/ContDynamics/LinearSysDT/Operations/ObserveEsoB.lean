import CORALean.ContDynamics.LinearSysDT.LinearSysDT
import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripLiu

/-!
# `LinearSysDT.observeEsoB`

One step of CORA's ellipsoidal observer `ESO-B` (`priv_observe_ESO_B`), corrected so that it
encloses the true state (`LinearSysDT.observeEsoB_outer`), on `E(Q, c)` at the level `1`:

* `post`: the shape `A Q Aᵀ` and the centre `A c + u` (the known input `B u + c` folded into `u`,
  as `LinearSysDT` folds it);
* the prediction `Q_next = (1 - p)⁻¹ A Q Aᵀ + p⁻¹ W` at any `p ∈ (0, 1)`, where the code has
  `(σ² p)⁻¹ W`, the prediction of the level-`σ²` set (Eq. 21 of Liu, Zhao and Wu, IET Control
  Theory & Applications, 2016); CORA's `p = √tr W / (√tr(σ² A Q Aᵀ) + √tr W)` (Eq. 48) is one
  choice;
* the code's trigger `σ²_prev + δᵀδ > 1` and the corrected update `Ellipsoid.intersectStripLiu`
  (Thm. 3) with the measurement noise `E(0, V)`, at the level `1` of the predicted set where the
  code passes its `sigma_sq` (`0.3` at the first step, which `R0` need not satisfy), at the weight
  `λ` (CORA's from Thm. 3 is one choice); otherwise the prediction `E(Q_next, A c + u)` unchanged.

`LinearSysDT.observeEsoB1D` is the step as the code computes it, with its counterexample.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def LinearSysDT.observeEsoB (sys : LinearSysDT ℝ n) (C : Mat ℝ m n)
    (W : Mat ℝ n n) (V : Mat ℝ m m) (p lam σsqPrev : ℝ) (u : Vec ℝ n) (y : Vec ℝ m)
    (Q : Mat ℝ n n) (c : Vec ℝ n) : Ellipsoid n :=
  let Qhom := sys.A * Q * sys.Aᵀ  -- `Rnext_hom = post(...)`: the shape of `A*Rnext.tp`
  let chom := sys.A *ᵥ c + u  -- its centre
  let Qnext := (1 - p)⁻¹ • Qhom + p⁻¹ • W  -- `Q_next`; the code has `(sigma_sq*p)^-1`
  let δ := y - C *ᵥ chom  -- `delta` of `aux_methodLiu2016`
  if σsqPrev + δ ⬝ᵥ δ > 1 then  -- Theorem 3 of Liu et al.
    Ellipsoid.intersectStripLiu Qnext chom C V y 1 lam  -- corrected; the code passes `sigma_sq`
  else Ellipsoid.ofShape Qnext chom  -- the ellipsoid is unchanged

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
