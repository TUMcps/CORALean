module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# `Interval.intersection`

Intersecting two boxes, coordinatewise and exactly: a point is in both when each
of its coordinates clears both lower bounds and stays under both upper ones.

The result may be empty, and says so the way this representation always does —
some coordinate's `sup` below its `inf`.

## Inputs
* `I₁` – first interval box
* `I₂` – second interval box

## Output
* box of the coordinatewise overlap
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.intersection (I₁ I₂ : Interval (Vec ℝ n)) : Interval (Vec ℝ n) where
  inf := fun j => max (I₁.inf j) (I₂.inf j)
  sup := fun j => min (I₁.sup j) (I₂.sup j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
