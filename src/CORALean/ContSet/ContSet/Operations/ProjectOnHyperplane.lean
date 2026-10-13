import CORALean.ContSet.ContSet.ContSet

/-!
# CORA's `projectOnHyperplane`: the orthogonal projection onto a hyperplane

CORA normalizes the hyperplane to unit normal `c` and offset `d` (`{x | cᵀ x = d}`), then
computes `A = I - c cᵀ`, `b = d c` and `S = A S + b`. Here the normalized normal and offset are
the arguments, the normalization being the caller's (it needs a square root of a float sum); the
operation is at the real scalar, as it multiplies entries of the supplied normal.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {S : ℕ → Type}
variable [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] {n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, OfPoint (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `projectOnHyperplane` for the hyperplane `{x | c ⬝ x = d}` of unit normal `c`:
`S = (I - c cᵀ) S + d c`. -/
noncomputable def ContSet.projectOnHyperplane (s : S n) (c : Vec ℝ n) (d : ℝ) : S n :=
  let A : Mat ℝ n n := 1 - Matrix.vecMulVec c c
  let b : Vec ℝ n := d • c
  Plus.plus (Mtimes.mtimes A s) (OfPoint.ofPoint b)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
