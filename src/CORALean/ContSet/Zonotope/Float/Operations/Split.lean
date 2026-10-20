module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.CenterResidual

@[expose] public section

/-!
# `Zonotope.split`, over a floating-point scalar

CORA's `aux_splitOneDim`: `c1 = c - G(:,dim)/2`, `c2 = c + G(:,dim)/2` and the `dim`-th
generator halved in both. Halving is exact in a binary format, so only the two centers round;
each half stores the lower directed sum and pays the `centerResidual` into its error box, which
leaves the generator count unchanged as over ℝ. The halves cover `Z` only after that inflation.

## Inputs
* `Z` – zonotope
* `j` – generator index

## Output
* two halves of the zonotope along generator `j`
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

def Zonotope.aux_splitHalf (Z : Zonotope (Vec 𝕋 n)) (j : Fin Z.h) (s : Vec 𝕋 n) :
    Zonotope (Vec 𝕋 n) where
  h := Z.h
  c := fun i => addDown (Z.c i) (s i)
  G := Function.update Z.G j fun i => half (Z.G j i)
  I_error := Z.I_error.plus (Zonotope.centerResidual Z.c s)


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two halves of `Z` along its `j`-th generator. -/
def Zonotope.split (Z : Zonotope (Vec 𝕋 n)) (j : Fin Z.h) : Zonotope (Vec 𝕋 n) ×
    Zonotope (Vec 𝕋 n) :=
  let g := fun i => half (Z.G j i)
  (Z.aux_splitHalf j (-g), Z.aux_splitHalf j g)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
