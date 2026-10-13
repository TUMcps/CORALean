module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.intersectStripGollamudi1D`

The update of CORA's `@ellipsoid/intersectStrip` (method `'Gollamudi1996'`,
`aux_methodGollamudi1996`) for `n = 1` and one strip, at the weight `λ` (CORA picks
`min(1e-4, ν)`), as the code computes it:
`δ = y - C c`, `σ² = 1 - λ + λ φ² - λ (1 - λ) δ² / ((1 - λ) + λ C Q C)`, the inverse shape
`(1 - λ) Q⁻¹ + λ C²`, the new centre `c + λ Q C δ` and the new shape `Q' / σ²`. It returns
the new centre and shape matrix `Q` of the ellipsoid `{x | (x - c)² / Q ≤ 1}`; the trigger
`σ²_prev + δ² > φ` and the choice of `λ` are left to the caller.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.intersectStripGollamudi1D (Q c C φ y lam : ℝ) : ℝ × ℝ :=
  let δ := y - C * c  -- innovation
  let Qtmp := (1 - lam) + lam * (C * Q * C)  -- `(1-λ) I + λ G`
  let σsq := 1 - lam + lam * φ ^ 2 - lam * (1 - lam) * δ * Qtmp⁻¹ * δ  -- `sigma_sq`
  let invQ := (1 - lam) * Q⁻¹ + lam * (C * C)  -- `(1-λ) Q⁻¹ + λ Cᵀ C`
  (c + lam * Q * C * δ, invQ⁻¹ / σsq)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
