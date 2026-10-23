module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.VPolytope.Float.Operations.ColumnGap
public import CORALean.ContSet.VPolytope.Float.Theorems.MemColumnGap
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_VPolytope
public import CORALean.ContSet.VPolytope.Real.Theorems.PerturbSubset
public import CORALean.ContSet.Interval.Real.Theorems.Convex
public import CORALean.ContSet.Interval.Float.Theorems.PlusOuter
public import CORALean.ContSet.Conversion.Real.Operations.HPolytope_to_VPolytope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_VPolytope

@[expose] public section

/-!
# A zonotope as its corners, over a floating-point scalar

## Inputs
* `Z` – zonotope
* `σ` – sign per generator
* `i` – coordinate
* `j` – generator index

## Output
* contribution of generator `j` to the corner
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generator's contribution to a corner, at its own sign. -/
def Zonotope.signed (Z : Zonotope (Vec 𝕋 n)) (σ : Fin Z.h → Bool) (i : Fin n) (j : Fin Z.h) : 𝕋 :=
  if σ j then Z.G j i else neg (Z.G j i)

/-- The lower rounded coordinate `i` of the corner of the zonotope picked by the sign pattern `l`.
-/
def Zonotope.cornerLo (Z : Zonotope (Vec 𝕋 n)) (l : Fin (2 ^ Z.h)) (i : Fin n) : 𝕋 :=
  addDown (Z.c i) (sumDown (Z.signed (signEquiv Z.h l) i))

/-- The upper rounded coordinate `i` of the corner of the zonotope picked by the sign pattern `l`.
-/
def Zonotope.cornerHi (Z : Zonotope (Vec 𝕋 n)) (l : Fin (2 ^ Z.h)) (i : Fin n) : 𝕋 :=
  addUp (Z.c i) (sumUp (Z.signed (signEquiv Z.h l) i))

/-- The hull of a zonotope's corners, stored as the rounded-down corners, with the gap to the
rounded-up corners and the zonotope's error added to the error box. -/
def Zonotope.vPolytope (Z : Zonotope (Vec 𝕋 n)) : VPolytope (Vec 𝕋 n) where
  k := 2 ^ Z.h
  V := Z.cornerLo
  I_error := (VPolytope.columnGap Z.cornerLo Z.cornerHi).plus Z.I_error

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
