import CORALean.ContSet.Zonotope.Real.Zonotope
import Mathlib.Data.Finset.Sort

/-!
# `Zonotope.filterGen`

The zonotope that keeps the generators a predicate selects, in their order, and the centre.
The building block of `compact_`: CORA's `nonzeroFilter(Z.G, tol)` is a column filter, and
dropping a generator whose column is zero changes no point (`filterGen_construct`).
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generators `j` with `keep j`, in order; the centre is unchanged. -/
def Zonotope.filterGen (Z : Zonotope α) (keep : Fin Z.h → Bool) : Zonotope α where
  h := (Finset.univ.filter fun j => keep j = true).card
  c := Z.c
  G := fun j => Z.G ((Finset.univ.filter fun j => keep j = true).orderEmbOfFin rfl j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
