module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.intersectStripLiu1D`

The update of CORA's `@ellipsoid/intersectStrip` (method `'Liu2016'`, `aux_methodLiu2016`) for
`n = 1` and one measurement, as the code computes it. The measurement set is
`{x | (y - C x)ᵀ V⁻¹ (y - C x) ≤ 1}`; the struct `sys` is the pair `V = sys.V` and
`barV = sys.bar_V` (`linearSysDT/priv_observe_ESO_B` passes `chol(inv(V))`). With `δ = y - C c`:
`G = barV C Q C barV`, `g = eigs(G,1) = G`, `β = (1 - σ²_prev)/δ²`, `ω = 1 + β (g - 1)`,
`λ = (1 - β)/2` if `withinTol(g,1)` (here exact equality) else `(1 - √(g/ω))/(1 - g)` (Thm. 3),
`Q_tmp = V/λ + C Q C/(1 - λ)` (Eq. 27), `K = Q C Q_tmp⁻¹/(1 - λ)` (Eq. 26),
`σ² = (1 - λ) σ²_prev + λ - δ Q_tmp⁻¹ δ` (Eq. 25), the shape `(1 - λ)(1 - K C) Q` (Eq. 24) and
the centre `c + K δ` (Eq. 23).

It returns the new centre, the new shape `Q` of `{x | (x - c)² / Q ≤ 1}` and `σ²`; the trigger
`σ²_prev + δ² > 1` is the caller's. The shape is `(1 - λ)²` times the one the fusion needs
(`intersectStripLiu1D_counterexample`, `intersectStripLiu`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.intersectStripLiu1D (Q c C V barV y σsqPrev : ℝ) : ℝ × ℝ × ℝ :=
  let δ := y - C * c  -- `delta`
  let G := barV * C * Q * C * barV  -- `G`, below eq. (51)
  let g := G  -- `eigs(G,1)`: `G` is `1 × 1`
  let β := (1 - σsqPrev) / (δ * δ)  -- `beta`, eq. (52)
  let ω := 1 + β * (g - 1)  -- `omega`
  let lam := if g = 1 then (1 - β) / 2 else 1 / (1 - g) * (1 - Real.sqrt (g / ω))  -- Thm. 3
  let Qtmp := 1 / lam * V + 1 / (1 - lam) * C * Q * C  -- `Q_tmp`, eq. (27)
  let QtmpInv := Qtmp⁻¹  -- `Q_tmp_inv`
  let K := 1 / (1 - lam) * Q * C * QtmpInv  -- `K`, eq. (26)
  let σsq := (1 - lam) * σsqPrev + lam - δ * QtmpInv * δ  -- `sigma_sq`, eq. (25)
  let Q' := (1 - lam) * (1 - K * C) * Q  -- new shape, eq. (24)
  let c' := c + K * δ  -- new centre, eq. (23)
  (c', Q', σsq)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
