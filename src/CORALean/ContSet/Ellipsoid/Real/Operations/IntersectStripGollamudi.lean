module

public import CORALean.ContSet.Ellipsoid.Real.Operations.OfShape

@[expose] public section

/-!
# `Ellipsoid.intersectStripGollamudi`

CORA's `@ellipsoid/intersectStrip` (method `'Gollamudi1996'`, `aux_methodGollamudi1996`) for an
ellipsoid of shape `Q` and centre `c` and the strip `‖C x - y‖₂ ≤ φ` (`C` is `m × n`), at the
weight `λ` (CORA picks `min(1e-4, ν)`; the trigger `σ²_prev + δᵀδ > φ` and the choice of `λ`
are left to the caller), corrected so that it encloses the intersection
(`intersectStripGollamudi_outer`). Every point of the intersection satisfies the convex
combination `(1 - λ)(x - c)ᵀ Q⁻¹ (x - c) + λ ‖C x - y‖₂² ≤ 1 - λ + λ φ²`, which completes to
`(x - c*)ᵀ invQ (x - c*) ≤ σ²` with

* `δ = y - C c`, `invQ = (1 - λ) Q⁻¹ + λ Cᵀ C`, as the code computes them,
* `σ² = 1 - λ + λ φ² - λ (1 - λ) δᵀ ((1 - λ) I + λ C Q Cᵀ)⁻¹ δ`, as the code computes it,
* the minimiser `c* = c + λ invQ⁻¹ Cᵀ δ`, where the code has `c + λ Q Cᵀ δ`,
* the shape `σ² invQ⁻¹`, where the code has `invQ⁻¹ / σ²`.

The two departures from the code are the corrections; `intersectStripGollamudi1D` is the update
as the code computes it, with its counterexample.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.intersectStripGollamudi (Q : Mat ℝ n n) (c : Vec ℝ n) (C : Mat ℝ m n)
    (φ : ℝ) (y : Vec ℝ m) (lam : ℝ) : Ellipsoid n :=
  let δ := y - C *ᵥ c  -- innovation `delta`
  let Qtmp := (1 - lam) • (1 : Mat ℝ m m) + lam • (C * Q * Cᵀ)  -- `(1-λ) I + λ G`
  let σsq := 1 - lam + lam * φ ^ 2 - lam * (1 - lam) * (δ ⬝ᵥ Qtmp⁻¹ *ᵥ δ)  -- `sigma_sq`
  let invQ := (1 - lam) • Q⁻¹ + lam • (Cᵀ * C)  -- `(1-λ) inv(Q) + λ C'C`
  let c' := c + lam • (invQ⁻¹ *ᵥ (Cᵀ *ᵥ δ))  -- the minimiser; the code has `Q` for `inv(invQ)`
  Ellipsoid.ofShape (σsq • invQ⁻¹) c'  -- `inv(invQ)*sigma_sq`; the code has `/sigma_sq`

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
