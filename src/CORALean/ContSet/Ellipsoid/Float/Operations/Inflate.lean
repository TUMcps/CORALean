module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# A shape matrix rounded upward

A float operation computes its shape matrix, `M Q Mᵀ` or `s₁² Q₁ + s₂² Q₂`, as an interval matrix
holding the exact one entry by entry; this stores a float matrix that dominates every symmetric
matrix in that interval. The upper bound of each entry of the upper triangle is mirrored, so the
stored matrix is symmetric, and each diagonal entry is raised by the widths of its row's other
brackets, so the difference to the exact matrix is diagonally dominant and hence positive
semi-definite (`Theorems/InflateSubPosSemidef`). By `Real.Ellipsoid.construct_subset_of_le` the
stored ellipsoid then contains the exact one: rounding is paid into `Q`, not into the error box.

## Inputs
* `X` – interval shape matrix

## Output
* symmetric float matrix above every symmetric matrix of `X`
-/

-- Authors:       Claude Opus 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A symmetric float matrix above every symmetric matrix of `X`, in the Loewner order. -/
def Ellipsoid.inflate (X : Interval (Mat 𝕋 n n)) : Mat 𝕋 n n :=
  -- the upper triangle's upper bounds, mirrored
  let up : Mat 𝕋 n n := fun i j => if i ≤ j then X.sup i j else X.sup j i
  -- the width of each entry's bracket, mirrored the same way
  let w : Mat 𝕋 n n := fun i j =>
    if i ≤ j then subUp (X.sup i j) (X.inf i j) else subUp (X.sup j i) (X.inf j i)
  -- each diagonal entry raised by its row's other widths
  let margin : Vec 𝕋 n := fun i => sumUp fun j => if j = i then zero else w i j
  fun i j => if i = j then addUp (up i i) (margin i) else up i j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
