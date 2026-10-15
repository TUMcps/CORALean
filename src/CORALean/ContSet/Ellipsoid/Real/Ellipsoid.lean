module

public import CORALean.Global.EuclideanNorm

@[expose] public section

/-!
# Ellipsoids: the representation

The definition is [1, Def. 4]: CORA's `ellipsoid` stores a shape matrix `Q` and a centre, which
[1] calls `c` and so does the field. CORALean stores the *generator* matrix `G` instead and
denotes the same family as the affine image of a Euclidean unit ball,

  `E = {c + G u | ‖u‖₂ ≤ 1}`,   `Q = G Gᵀ`.

The generator form needs no matrix inverse, no positive-semi-definiteness side
condition to carry through every operation, and no matrix square root to get
back out of one. A degenerate ellipsoid is a singular `G` and costs nothing.

`G` is `n × k` with `k` a field, as the zonotope's generator count is. That is
what makes a linear image exact without a square root: `M G` is `m × k`, where a
square `G` would have forced one back in.

`‖·‖₂` is `CORALean.norm₂`, deliberately not `‖·‖`: `Vec ℝ n` is `Fin n → ℝ` and
carries the supremum norm.

## References

* [1] M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated
      Verification of Linear Systems Using Reachability Analysis with Support
      Functions". HSCC, 2023, Article 5.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure Ellipsoid (n : ℕ) where
  k : ℕ
  c : Vec ℝ n
  G : Mat ℝ n k

def Ellipsoid.construct (E : Ellipsoid n) : Set (Vec ℝ n) :=
  {x | ∃ u : Vec ℝ E.k, ‖u‖₂ ≤ 1 ∧ x = E.c + E.G *ᵥ u}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
