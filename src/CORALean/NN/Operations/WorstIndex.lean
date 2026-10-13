import CORALean.Global.Tensor
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic

/-!
# The largest-ranked of a fixed number of candidates

Shared by both refinement rules: `RefineWorst` ranks layers with it and
`RefineWorstNeurons` ranks `(layer, neuron)` pairs, each reading it at a
different `r`.

Sorts on the negated rank: `Tuple.sort` is total, so `0` is largest, and ties
go to the earlier index.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {k : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The largest-ranked of `k + 1` candidates, ties to the earlier one, which is
what `Tuple.sort` gives at index `0`. -/
noncomputable def worstIndex (r : Fin (k + 1) → ℝ) : Fin (k + 1) :=
  (Tuple.sort fun l => -r l) 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
