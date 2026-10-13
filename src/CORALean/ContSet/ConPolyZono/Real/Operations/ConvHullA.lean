import CORALean.ContSet.ConPolyZono.Real.Operations.BlkDiag

/-!
# `ConPolyZono.convHullA`

The constraint matrix of [1, Prop. 9]: the linear combination's, once per copy
on the diagonal, and one last row of ones over the weight columns — the row that
says the `a` weights sum to what a convex combination needs.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       13-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One copy of `A` per block, and a final row summing the weights. -/
def ConPolyZono.convHullA (a : ℕ) {m s : ℕ} (A : Mat ℝ m s) : Mat ℝ (a * m + 1) (a * s + a) :=
  fun x => Fin.append
    (fun r => Fin.append (ConPolyZono.blkDiag a A r) (fun _ => (0 : ℝ)))
    (fun _ => Fin.append (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))) x

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
