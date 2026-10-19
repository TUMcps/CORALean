module

public import CORALean.ContSet.Ellipsoid.Real.Ellipsoid

@[expose] public section

/-!
# The ellipsoid of a factored shape matrix

`ofFactor F q` is the ellipsoid of shape `F Fᵀ` and center `q`, for any `n × k` matrix `F`: the
shape matrix CORA computes as `G*G'` from generators `G` (`zonotope/ellipsoid`, `fac*(G*G')`), and
positive semi-definite on sight. `construct_ofFactor` says it is `{q + F u | ‖u‖₂ ≤ 1}`.

## Inputs
* `F` – factor
* `q` – center

## Output
* ellipsoid of shape `F Fᵀ` and center `q`
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The ellipsoid `ellipsoid(F*F', q)`. -/
def Ellipsoid.ofFactor (F : Mat ℝ n k) (q : Vec ℝ n) : Ellipsoid n where
  Q := F * Fᵀ
  q := q
  psd := by simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose F

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
