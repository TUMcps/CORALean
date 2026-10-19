module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
# The ellipsoid with a given shape matrix, checked

CORA's constructor `ellipsoid(Q, q)` for a `Q` computed rather than known: it checks that `Q` is
positive semi-definite and errors otherwise. The papers' `E(Q, q) = {x | (x − q)ᵀ Q⁻¹ (x − q) ≤ 1}`
([1, Eq. 5], [2, Sec. 1.1 (ellipse)]) is this for positive definite `Q` (`mem_ofShape_iff`). Where
CORA errors this returns the point `q`; no statement reads that case, every theorem about `ofShape`
assuming `Q` positive semi-definite, where it is the structure itself (`ofShape_eq`).

## Inputs
* `Q` – positive semi-definite shape
* `q` – center

## Output
* ellipsoid of shape `Q` and center `q`

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of
      Minkowski sum of ellipsoids". In Proc. of the 57th IEEE Conference on Decision and
      Control (CDC), pp. 4040-4045, 2018. arXiv:1803.08157.
* [2] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 48(5):890-906, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped MatrixOrder

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The ellipsoid of shape `Q` and center `q`, where `Q` is positive semi-definite. -/
noncomputable def Ellipsoid.ofShape (Q : Mat ℝ n n) (q : Vec ℝ n) : Ellipsoid n :=
  open Classical in
  if hQ : Q.PosSemidef then ⟨Q, q, hQ⟩ else ⟨0, q, .zero⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
