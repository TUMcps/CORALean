import CORALean.NN.Graph.Operations.Ball

/-!
# A node no edge points at never joins the ball

`ball`'s successor case adds `j` from an already-present `i` via `A i j ≠ 0` —
the edge read *into* the new node, not out of it. So the hypothesis has to be
about `A i w`, the column at `w`, not the row: a node whose row is all zero
but whose column is not can still be reached by an edge running the other way.
Induction on the radius, mirroring `mem_ball_self`.

This is what lets a caller *omit* an isolated node from an enumeration: it
never joins the ball at any radius, so nothing else has to say so again.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- No edge points at `w` and `w` is not the centre, so `w` never joins the ball. -/
theorem GNN.not_mem_ball_of_isolated {N : ℕ} (A : Mat ℝ N N) (v : Fin N) {w : Fin N}
    (hw : ∀ i, A i w = 0) (hwv : w ≠ v) (r : ℕ) : w ∉ GNN.ball A v r := by -- --- PROOF ---
  induction r with
  | zero => simpa [GNN.ball] using hwv
  | succ r ih =>
      intro hmem
      obtain ⟨_, i, hi, hcase⟩ := Finset.mem_filter.mp hmem
      rcases hcase with heq | hne
      · exact ih (heq ▸ hi)
      · exact hne (hw i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
