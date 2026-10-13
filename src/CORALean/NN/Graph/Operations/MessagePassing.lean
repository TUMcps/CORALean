import CORALean.NN.Graph.Operations.Degree
import Mathlib.Analysis.Real.Sqrt

/-!
# `P = D̃^(-1/2) Ã D̃^(-1/2)`, entrywise

[1, Eq. 2]'s message passing at a known graph, `D̃` being diagonal: entry `(i, j)`
of `Ã = A + I` scaled by both endpoints' inverse square-root degrees.

## References

* [1] T. N. Kipf and M. Welling. "Semi-Supervised Classification with Graph
      Convolutional Networks". ICLR, 2017.
-/

-- Authors:       Claude Sonnet 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `P = D̃^(-1/2) Ã D̃^(-1/2)`, entrywise, `D̃` being diagonal. -/
noncomputable def GNN.messagePassing (A : Mat ℝ N N) : Mat ℝ N N :=
  fun i j => (A + 1) i j / (Real.sqrt (GNN.degree A i) * Real.sqrt (GNN.degree A j))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
