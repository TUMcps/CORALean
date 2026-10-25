module

public import CORALean.ContSet.Ellipsoid.Real.Operations.OfShape

@[expose] public section

/-!
# The checked constructor at a positive semi-definite shape

`Ellipsoid.ofShape Q q` is the ellipsoid of shape `Q` and center `q` when `Q` is positive
semi-definite, the papers' `E(Q, q)` ([1, Eq. 5], [2, Sec. 1.1 (ellipse)]).

## Inputs
* `Q` – shape matrix
* `q` – center

## Hypotheses
* `hQ` – `Q` positive semi-definite

## Conclusion
* the checked constructor is the structure with fields `Q`, `q`

## References

* [1] A. Halder. "On the parameterized computation of minimum volume outer ellipsoid of Minkowski
      sum of ellipsoids". 2018 IEEE Conference on Decision and Control (CDC), 2018.
* [2] M. Černý. "Goffin's algorithm for zonotopes". Kybernetika, 2012.
-/

-- Authors:       Claude Opus 5.5
-- Written:       08-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix
open scoped MatrixOrder

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- At a positive semi-definite `Q` the checked constructor is the structure itself. -/
theorem Ellipsoid.ofShape_eq {Q : Mat ℝ n n} (hQ : Q.PosSemidef) (q : Vec ℝ n) :
    Ellipsoid.ofShape Q q = ⟨Q, q, hQ⟩ :=
  dif_pos hQ

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
