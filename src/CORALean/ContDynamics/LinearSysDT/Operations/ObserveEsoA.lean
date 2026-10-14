module

public import CORALean.ContDynamics.LinearSysDT.LinearSysDT
public import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripGollamudi

@[expose] public section

/-!
# `LinearSysDT.observeEsoA`

One step of CORA's ellipsoidal observer `ESO-A` (`priv_observe_ESO_A`), corrected so that it
encloses the true state (`LinearSysDT.observeEsoA_outer`). The estimate is CORA's ellipsoid
`E(Q, c)`, at the level `1`, as `aux_methodGollamudi1996` reads its input. The step:

* `post`: the shape `A Q Aᵀ` and the centre `A c + B u + c_sys` (`B` and the offset `c_sys`
  the system's, as CORA's `post` adds them; `C` too is the system's);
* the prediction `Q_next = (1 - p)⁻¹ A Q Aᵀ + p⁻¹ W` at any `p ∈ (0, 1)`, where the code has
  `(σ² p)⁻¹ W`: dividing by `σ²` is the step to the level-`σ²` sets of Liu, Zhao and Wu (IET
  Control Theory & Applications, 2016), which the Gollamudi update does not use; CORA's
  `p = √tr W / (√tr(σ² A Q Aᵀ) + √tr W)` is one choice;
* the code's trigger `σ²_prev + δᵀδ > φ` (`φ = norm(params.V)`) and the corrected strip update
  `Ellipsoid.intersectStripGollamudi` at the weight `λ` (CORA's `min(1e-4, ν)` is one choice);
  otherwise the prediction `E(Q_next, A c + u)` unchanged.

`LinearSysDT.observeEsoA1D` is the step as the code computes it, with its counterexample.
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

noncomputable def LinearSysDT.observeEsoA (sys : LinearSysDT ℝ n)
    (W : Mat ℝ n n) (φ p lam σsqPrev : ℝ) (u : Vec ℝ sys.m) (y : Vec ℝ sys.q)
    (Q : Mat ℝ n n)
    (c : Vec ℝ n) : Ellipsoid n :=
  let Qhom := sys.A * Q * sys.Aᵀ  -- `Rnext_hom = post(...)`: the shape of `A*Rnext.tp`
  let chom := sys.A *ᵥ c + (sys.B *ᵥ u + sys.c)  -- its centre, `A c + B u + c`
  let Qnext := (1 - p)⁻¹ • Qhom + p⁻¹ • W  -- `Q_next`; the code has `(sigma_sq*p)^-1`
  let δ := y - sys.C *ᵥ chom  -- `delta` of `aux_methodGollamudi1996`
  if σsqPrev + δ ⬝ᵥ δ > φ then  -- Theorem 2 of Gollamudi et al.
    Ellipsoid.intersectStripGollamudi Qnext chom sys.C φ y lam  -- the corrected update
  else Ellipsoid.ofShape Qnext chom  -- the ellipsoid is unchanged

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
