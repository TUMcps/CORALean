module

public import CORALean.ContSet.Ellipsoid.Real.Operations.IntersectStripGollamudi1D

@[expose] public section

/-!
# `LinearSysDT.observeEsoA1D`

One step of CORA's ellipsoidal observer `ESO-A` (`linearSysDT/executeObserver` with
`options.alg = 'ESO-A'`, `priv_observe_ESO_A`) for `n = 1`, as the code computes it: from the
estimate `E(Q, c)` (`{x | (x - c)² / Q ≤ 1}`) and the previous `σ²_prev`, the prediction the code
takes from Eq. 21 and Eq. 48 of Liu, Zhao and Wu (IET Control Theory & Applications, 2016),

  `Q_next = (1 - p)⁻¹ A Q A + (σ²_prev p)⁻¹ W`,  `p = √W / (√(σ²_prev A Q A) + √W)`,

centred at `A c + u` (`post`: `A x + B u + c`, the known input folded into `u`), then the strip
update the code takes from Gollamudi, Nagaraj, Kapoor and Huang (ISITA 1996), by
`intersectStrip(…, 'Gollamudi1996')` with `phi = norm(params.V) = √V` for the measurement noise
`E(0, V)`: the trigger `σ²_prev + δ² > phi`, the weight `λ = min(1e-4, ν)` and the update
`Ellipsoid.intersectStripGollamudi1D`. It returns the new centre, shape and `sigma_sq`. The update
divides the shape by `σ²` where the enclosure needs `σ²` times it
(`Ellipsoid.intersectStripGollamudi1D_counterexample`); the observer inherits that
(`LinearSysDT.observeEsoA1D_counterexample`). `LinearSysDT.observeEsoA` is the corrected step.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def LinearSysDT.observeEsoA1D (A C W V u y Q c σsqPrev : ℝ) : ℝ × ℝ × ℝ :=
  let phi := Real.sqrt V  -- `phi = norm(params.V)`
  let auxRes := Real.sqrt W  -- `auxRes = sqrt(trace(params.W.Q))`
  let Qhom := A * Q * A  -- `Rnext_hom = post(...)`: the shape of `A*Rnext.tp`
  let chom := A * c + u  -- its centre, `B u + c` folded into `u`
  let p := auxRes / (Real.sqrt (σsqPrev * Qhom) + auxRes)  -- `p`, eq. (48) of Liu et al.
  let Qnext := (1 - p)⁻¹ * Qhom + (σsqPrev * p)⁻¹ * W  -- `Q_next`
  let δ := y - C * chom  -- `delta` of `aux_methodGollamudi1996`
  if σsqPrev + δ * δ > phi then  -- Theorem 2 of Gollamudi et al.
    let α : ℝ := 1 / 10000  -- `alpha = 1e-4`
    let G := C * Qnext * C  -- `G`
    let g := |G|  -- `svds(G,1)`
    let β := (phi - σsqPrev) / (δ * δ)  -- `beta`, eq. (18) of Gollamudi et al.
    let ω := 1 + β * (g - 1)  -- `omega`
    let ν := if δ = 0 then α else if g = 1 then (1 - β) / 2
      else if ω > 0 then 1 / (1 - g) * (1 - Real.sqrt (g / ω)) else α  -- `nu`
    let lam := min α ν  -- `lambda`
    let Qtmp := (1 - lam) + lam * G  -- `Q_tmp`
    let σsq := 1 - lam + lam * phi ^ 2 - lam * (1 - lam) * δ * Qtmp⁻¹ * δ  -- `sigma_sq`
    let E := Ellipsoid.intersectStripGollamudi1D Qnext chom C phi y lam  -- `E.q`, `E.Q`
    (E.1, E.2, σsq)
  else (chom, Qnext, σsqPrev)  -- the ellipsoid is unchanged

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
