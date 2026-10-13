module

public import CORALean.ContSet.Zonotope.Real.Operations.CompactZeros
public import CORALean.ContSet.Zonotope.Real.Theorems.FilterGenConstruct

@[expose] public section

/-!
# `compact_(Z, 'zeros')` at tolerance `0` changes no point

Exact: the dropped generators are zero, and `Zonotope.filterGen_construct` says dropping zero
generators denotes the same set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open scoped Classical

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.compactZeros_exact (Z : Zonotope α) :
    Z.compactZeros.construct = Z.construct :=
  Z.filterGen_construct _ fun j hj => by simpa using hj

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
