module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# A box as a zonotope — the construction

`Interval.zonotope` is the construction; `Interval_to_Zonotope` states and proves what it
guarantees.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Interval.zonotope (I : Interval (Vec ℝ n)) : Zonotope (Vec ℝ n) where
  h := n
  c := fun i => (I.inf i + I.sup i) / 2
  G := fun j i => if i = j then (I.sup i - I.inf i) / 2 else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
