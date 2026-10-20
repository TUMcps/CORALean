module

public import CORALean.ContSet.Zonotope.Real.Theorems.MemConstruct
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# A zonotope as a box

## Inputs
* `Z` – zonotope

## Output
* interval of the zonotope
-/

-- Authors:       Claude Opus 5
-- Written:       16-August-2026
-- Last update:   12-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Zonotope.interval (Z : Zonotope α) : Interval α where
  inf := ofEntry fun i => entry Z.c i - ∑ j, |entry (Z.G j) i|
  sup := ofEntry fun i => entry Z.c i + ∑ j, |entry (Z.G j) i|

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
