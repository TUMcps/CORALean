module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# The matrix of some columns followed by one more

The square matrix whose first `m` columns are `B 0, …, B (m - 1)` and whose last is `x`. The
determinants `det [B_i σλ]` and `det [B_i v_i]` of the volume formula [1, Sec. 6.1] are of this
form, `B_i` being the `n - 1` generators a subset picks out.

## Inputs
* `B` – list of column vectors
* `x` – appended last column

## Output
* square matrix with those columns

## References

* [1] [T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica,
      2005.](../../../../../../references/2005/alamo-automatica-guaranteed-estimation.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[B 0 … B (m-1)  x]`, the vectors as columns. -/
abbrev colsSnoc (B : Fin m → Vec ℝ (m + 1)) (x : Vec ℝ (m + 1)) : Mat ℝ (m + 1) (m + 1) :=
  Matrix.of fun i k => (Fin.snoc (α := fun _ => Vec ℝ (m + 1)) B x k) i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
