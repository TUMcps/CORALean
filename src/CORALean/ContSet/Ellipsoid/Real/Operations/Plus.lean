module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# `Ellipsoid.plus`

The Minkowski sum of two ellipsoids is not an ellipsoid, so CORA's
`@ellipsoid/plus` encloses it, and every enclosure carries a free parameter.
Here that parameter is two scalings `s₁` and `s₂`, the shape matrix being
`s₁² Q₁ + s₂² Q₂`, and what they owe is `1/s₁² + 1/s₂² ≤ 1`, which is what `plus_outer` asks.

That admissible set is two-dimensional. Kurzhanski and Varaiya's
`Q(l) = (1 + 1/l) Q₁ + (1 + l) Q₂`, `l > 0`, which CORA's `priv_plusEllipsoid` computes for each
direction, sweeps one curve through it — `s₁ = √(1+1/l)`, `s₂ = √(1+l)`, along the boundary where
the sum is one; `plus_scalings_admissible` is what puts an `l` back on it.

The pair stays an argument: `Plus` has no room for it, and fixing it would bury
a precision choice in an interface, which is why `Instances` leaves it alone.
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
