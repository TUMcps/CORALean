import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

/-!
# `Ellipsoid.plus`

The Minkowski sum of two ellipsoids is not an ellipsoid, so CORA's
`@ellipsoid/plus` encloses it, and every enclosure carries a free parameter.
Here that parameter is the two generator scalings themselves, `s₁` and `s₂`,
and what they owe is `1/s₁² + 1/s₂² ≤ 1`, which is what `plus_outer` asks.

That admissible set is two-dimensional. Kurzhanski and Varaiya's
`Q(l) = (1 + 1/l) Q₁ + (1 + l) Q₂`, `l > 0`, sweeps one curve through it —
`s₁ = √(1+1/l)`, `s₂ = √(1+l)`, along the boundary where the sum is one;
`plus_scalings_admissible` is what puts an `l` back on it.

In shape-matrix form `Q` would have to be square-rooted back into a generator
matrix. In generator form it is not: `s₁²G₁G₁ᵀ + s₂²G₂G₂ᵀ` is `H Hᵀ` for
`H = [s₁ G₁ | s₂ G₂]` outright, so the generator count adds as a zonotope's.

The pair stays an argument: `Plus` has no room for it, and fixing it would bury
a precision choice in an interface, which is why `Instances` leaves it alone.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Ellipsoid.plus (s₁ s₂ : ℝ) (E₁ E₂ : Ellipsoid n) : Ellipsoid n where
  k := E₁.k + E₂.k
  q := E₁.q + E₂.q
  G := Matrix.of fun i =>
    Fin.append (fun j => s₁ * E₁.G i j) (fun j => s₂ * E₂.G i j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
