import CORALean.Global.EuclideanNorm

/-!
# Ellipsoids: the representation

CORA's `ellipsoid` stores a positive semi-definite shape matrix `Q` and a centre
`q`. CORALean stores the *generator* matrix `G` instead and denotes the same
family as the affine image of a Euclidean unit ball,

  `E = {q + G u | ‖u‖₂ ≤ 1}`,   `Q = G Gᵀ`.

The generator form needs no matrix inverse, no positive-semi-definiteness side
condition to carry through every operation, and no matrix square root to get
back out of one. A degenerate ellipsoid is a singular `G` and costs nothing.

`G` is `n × k` with `k` a field, as the zonotope's generator count is. That is
what makes a linear image exact without a square root: `M G` is `m × k`, where a
square `G` would have forced one back in.

`‖·‖₂` is `CORALean.norm₂`, deliberately not `‖·‖`: `Vec ℝ n` is `Fin n → ℝ` and
carries the supremum norm.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix

variable {n : ℕ}

structure Ellipsoid (n : ℕ) where
  k : ℕ
  q : Vec ℝ n
  G : Mat ℝ n k

def Ellipsoid.construct (E : Ellipsoid n) : Set (Vec ℝ n) :=
  {x | ∃ u : Vec ℝ E.k, ‖u‖₂ ≤ 1 ∧ x = E.q + E.G *ᵥ u}

end CORALean.Real
