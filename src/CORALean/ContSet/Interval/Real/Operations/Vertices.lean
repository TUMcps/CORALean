module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `Interval.vertices`

CORA's `@intervalMatrix/vertices`: the vectorised interval's vertices, `unique` rows, reshaped to
matrices. The vertices are the matrices every entry of which is an end of its entry's interval;
a `Finset` removes the repetitions `unique` removes (an entry with `inf = sup` has one end). CORA's
order is that of `unique`, which a set does not keep.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

open Classical in
/-- The corners of the box as matrices, without repetition. -/
noncomputable def Interval.vertices (A : Interval (Mat ℝ m n)) : Finset (Mat ℝ m n) :=
  Finset.univ.image fun σ : Fin m → Fin n → Bool =>
    (fun i j => if σ i j then A.sup i j else A.inf i j : Mat ℝ m n)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
