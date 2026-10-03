import CORALean.ContSet.Zonotope.Real.Operations.CompactZeros
import CORALean.ContSet.Zonotope.Real.Theorems.FilterGenConstruct

/-!
# `compact_(Z, 'zeros')` at tolerance `0` changes no point

Exact: the dropped generators are zero, and `Zonotope.filterGen_construct` says dropping zero
generators denotes the same set.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


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
