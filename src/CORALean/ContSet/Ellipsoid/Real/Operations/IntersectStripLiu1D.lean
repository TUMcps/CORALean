module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.intersectStripLiu1D`

The update of CORA's `@ellipsoid/intersectStrip` (method `'Liu2016'`) for `n = 1` and one
measurement, as the code computes it, with the measurement set `{x | (y - C x)ᵀ V⁻¹ (y - C x) ≤ 1}`,
`V = sys.V`, `barV = sys.bar_V`. With `δ = y - C c`: `G = barV C Q C barV`, `g = G`, `β = (1 -
σ²_prev)/δ²`, `ω = 1 + β (g - 1)`, `λ = (1 - β)/2` if `g = 1` else `(1 - √(g/ω))/(1 - g)` (Thm. 3),
`Q_tmp = V/λ + C Q C/(1 - λ)`, `K = Q C Q_tmp⁻¹/(1 - λ)`, `σ² = (1 - λ) σ²_prev + λ - δ Q_tmp⁻¹ δ`,
the shape `(1 - λ)(1 - K C) Q` and the center `c + K δ`. It returns the center, the shape and `σ²`;
the trigger `σ²_prev + δ² > 1` is the caller's. The shape is `(1 - λ)²` times the one the fusion
needs (`intersectStripLiu1D_counterexample`).

## Inputs
* `Q` – shape
* `c` – center
* `C` – measurement factor
* `V` – measurement covariance
* `barV` – factor of the inverse covariance
* `y` – measurement
* `σsqPrev` – previous level

## Output
* new center, shape and level
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
  let c' := c + K * δ  -- new center, eq. (23)
  (c', Q', σsq)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
