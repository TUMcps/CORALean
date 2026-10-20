module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# `Interval.submatrix`, an interval matrix on chosen rows and columns
Both bounds read at the chosen rows and columns, which is exact: the box of the submatrix is the
submatrix of the box.

## Inputs
* `I` – interval matrix
* `r` – row selection
* `c` – column selection

## Output
* interval matrix on the selected rows and columns
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} {m n m' n' : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.submatrix (I : Interval (Mat 𝕋 m n)) (r : Fin m' → Fin m) (c : Fin n' → Fin n) :
    Interval (Mat 𝕋 m' n') where
  inf := fun i j => I.inf (r i) (c j)
  sup := fun i j => I.sup (r i) (c j)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
