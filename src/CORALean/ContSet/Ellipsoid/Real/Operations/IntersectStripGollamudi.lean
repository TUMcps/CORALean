module

public import CORALean.ContSet.Ellipsoid.Real.Operations.OfShape

@[expose] public section

/-!
# `Ellipsoid.intersectStripGollamudi`

CORA's `@ellipsoid/intersectStrip` (method `'Gollamudi1996'`) for an ellipsoid of shape `Q` and
center `c` and the strip `‖C x - y‖₂ ≤ φ`, at the weight `λ` (the trigger and the choice of `λ` are
the caller's), corrected so that it encloses the intersection (`intersectStripGollamudi_outer`).
With `δ = y - C c`, `invQ = (1 - λ) Q⁻¹ + λ Cᵀ C` and `σ² = 1 - λ + λ φ² - λ (1 - λ) δᵀ ((1 - λ) I +
λ C Q Cᵀ)⁻¹ δ`, as the code computes them, the result has the minimiser `c* = c + λ invQ⁻¹ Cᵀ δ`,
where the code has `c + λ Q Cᵀ δ`, and the shape `σ² invQ⁻¹`, where the code has `invQ⁻¹ / σ²`.
These two departures are the corrections; `intersectStripGollamudi1D` is the update as coded, with
its counterexample.

## Inputs
* `Q` – shape matrix
* `c` – center
* `C` – measurement matrix
* `φ` – strip half-width
* `y` – measurement
* `lam` – update weight

## Output
* ellipsoid enclosing the intersection of `E` with the strip
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
