module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# `Zonotope.filterGen`

The zonotope that keeps the generators a predicate selects, in their order, and the centre.
The building block of `compact_`: CORA's `nonzeroFilter(Z.G, tol)` is a column filter, and
dropping a generator whose column is zero changes no point (`filterGen_construct`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
