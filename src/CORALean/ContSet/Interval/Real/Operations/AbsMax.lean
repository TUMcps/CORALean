import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.absMax`

A single matrix dominating every member of the box: the entrywise max of the
two endpoints' absolute values. `matPow`/`matMul` bound different members of
`A` independently, so a uniform norm bound over the whole interval matrix has
to go through one fixed dominating matrix rather than any one member of it —
this is that matrix, and `Theorems/NormLeAbsMax` is what it is for.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The entrywise max of `|inf|` and `|sup|`, non-negative and at least as big
as either endpoint's absolute value. -/
noncomputable def Interval.absMax (A : Interval (Mat ℝ m n)) : Mat ℝ m n :=
  fun i j => max |A.inf i j| |A.sup i j|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
