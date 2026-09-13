import CORALean.ContSet.ConPolyZono.Real.Operations.BlkDiag
import CORALean.ContSet.ConPolyZono.Real.Operations.SumRep

/-!
# A row of a block-diagonal matrix

The mirror of `prod_blkDiag` on the constraint side: a row of `blkDiag A` reads
only its own block of constraint generators, so the row of [1, Prop. 9]'s
constraint matrix belonging to copy `j` is the linear combination's row, over
copy `j`'s monomials.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       13-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- Block `j`'s row of `blkDiag A` pairs with block `j`'s entries alone. -/
theorem ConPolyZono.mulVec_blkDiag {a m s : ℕ} (A : Mat ℝ m s) (u : Fin (a * s) → ℝ)
    (j : Fin a) (i : Fin m) :
    (∑ y, ConPolyZono.blkDiag a A (finProdFinEquiv (j, i)) y * u y)
      = ∑ l, A i l * u (finProdFinEquiv (j, l)) := by -- --- PROOF ---
  rw [ConPolyZono.sum_rep (fun y => ConPolyZono.blkDiag a A (finProdFinEquiv (j, i)) y * u y)]
  refine (Finset.sum_eq_single j (fun j' _ hj' => ?_)
    (fun h => absurd (Finset.mem_univ j) h)).trans ?_
  -- every other block meets this row at zero
  · exact Finset.sum_eq_zero fun l _ => by simp [ConPolyZono.blkDiag, Ne.symm hj']
  · exact Finset.sum_congr rfl fun l _ => by simp [ConPolyZono.blkDiag]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
