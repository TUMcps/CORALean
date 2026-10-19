module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# CORA's `minus` with a vector subtrahend

`S + (-p)`, the point entering as a singleton. CORA throws for any other subtrahend (a Minkowski
difference is `minkDiff`), so the set minus a set is not defined here either.

## Inputs
* `s` – set
* `p` – numeric offset

## Output
* `s` shifted by `-p`
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar

variable {S α : Type} [AddCommGroup α] [Module ℝ α] [ContSet S α] [Plus S α] [OfPoint S α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `minus` for a numeric `p`: `S = S + (-p)`. -/
def ContSet.minus (s : S) (p : α) : S :=
  Plus.plus s (OfPoint.ofPoint (-p))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
