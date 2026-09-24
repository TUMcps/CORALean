import CORALean.NN.Graph.Operations.MessagePassing

/-!
# A nonzero message reads off `Ã`, not the division

`messagePassing`'s numerator is `(A + 1) i j`, and dividing by a nonzero
denominator (`GNN.one_le_degree` keeps both factors positive whenever `A` is
nonnegative, but nothing here even needs that) never turns a zero numerator
nonzero. Off the diagonal `(1 : Mat ℝ N N) i j = 0`, so the numerator is `A i j`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- A message from `i` to `j` reads either the self-loop or an edge of `A`. -/
theorem GNN.messagePassing_ne_zero {N : ℕ} (A : Mat ℝ N N) (i j : Fin N)
    (h : GNN.messagePassing A i j ≠ 0) : i = j ∨ A i j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine h ?_
  simp [GNN.messagePassing, Matrix.add_apply, Matrix.one_apply_ne hcon.1, hcon.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
