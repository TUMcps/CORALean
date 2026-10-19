module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.plus`

The Minkowski sum of two ellipsoids is not an ellipsoid, so CORA's `@ellipsoid/plus` encloses it
with a free parameter: two scalings `s₁` and `s₂`, the shape matrix `s₁² Q₁ + s₂² Q₂`, owing `1/s₁²
+ 1/s₂² ≤ 1`, which is what `plus_outer` asks. Kurzhanski and Varaiya's `Q(l) = (1 + 1/l) Q₁ + (1 +
l) Q₂`, `l > 0`, which CORA's `priv_plusEllipsoid` computes for each direction, sweeps one curve
through that set — `s₁ = √(1+1/l)`, `s₂ = √(1+l)`; `plus_scalings_admissible` puts an `l` back on
it. The pair stays an argument: fixing it would bury a precision choice in an interface, which is
why `Instances` leaves it alone.

## Inputs
* `s₁` – scaling of `E₁`
* `s₂` – scaling of `E₂`
* `E₁` – first ellipsoid
* `E₂` – second ellipsoid

## Output
* ellipsoid of shape `s₁² Q₁ + s₂² Q₂` enclosing the sum
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.plus (s₁ s₂ : ℝ) (E₁ E₂ : Ellipsoid n) : Ellipsoid n where
  Q := s₁ ^ 2 • E₁.Q + s₂ ^ 2 • E₂.Q
  q := E₁.q + E₂.q
  psd := (E₁.psd.smul (sq_nonneg s₁)).add (E₂.psd.smul (sq_nonneg s₂))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
