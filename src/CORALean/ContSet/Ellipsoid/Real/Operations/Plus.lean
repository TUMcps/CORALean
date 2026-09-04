import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# `Ellipsoid.plus`

The Minkowski sum of two ellipsoids is not an ellipsoid, so CORA's
`@ellipsoid/plus` encloses it, and every enclosure of it carries a free
parameter. The classical family is Kurzhanski and Varaiya's

  `Q(l) = (1 + 1/l) Q₁ + (1 + l) Q₂`,   `l > 0`,

whose members are each tight in one direction and none in all: at
`l = ‖G₂ᵀ d‖₂ / ‖G₁ᵀ d‖₂` the support value in `d` is the sum's own.

In shape-matrix form `Q(l)` would have to be square-rooted back into a generator
matrix. In generator form it does not: `(1 + 1/l) G₁G₁ᵀ + (1 + l) G₂G₂ᵀ` is
`H Hᵀ` for `H = [√(1+1/l) G₁ | √(1+l) G₂]` outright, so only the two *scalars*
are square-rooted and the generator count adds, exactly as a zonotope's does.

`l` stays an argument: `Plus` has no room for it, and any fixed value would bury
a precision choice in an interface, which is why `Instances` leaves it alone.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

noncomputable def Ellipsoid.plus (l : ℝ) (E₁ E₂ : Ellipsoid n) : Ellipsoid n where
  k := E₁.k + E₂.k
  q := E₁.q + E₂.q
  G := Matrix.of fun i =>
    Fin.append (fun j => Real.sqrt (1 + 1 / l) * E₁.G i j)
      (fun j => Real.sqrt (1 + l) * E₂.G i j)

end CORALean.Real
