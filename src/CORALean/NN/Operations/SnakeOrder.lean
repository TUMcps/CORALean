import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Rev

/-!
# The inward spiral over a matrix

CORA's `snake` order of `getInputNeuronOrder`: take the first row of `A`, then turn the rest
`A(2:end,:)` a quarter turn, `A ← fliplr(A(2:end,:))'`, and repeat until nothing is left. The
matrix is a function on `Fin h × Fin w`, so the turn is index arithmetic: row `i` of the new
matrix, of which there are `w`, is column `w-1-i` of the old rest, read top to bottom.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {α : Type}


-- =====================================  MAIN DEFINITION  ====================================== --

def snakeOrder : (h w : ℕ) → (Fin h → Fin w → α) → List α
  | 0, _, _ => []
  | h + 1, w, A =>
    -- the first row, then the rest of the matrix turned a quarter turn
    List.ofFn (A 0) ++ snakeOrder w h fun i j => A j.succ (Fin.rev i)
termination_by h w => h + w

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
