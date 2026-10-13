import CORALean.ContSet.Zonotope.Float.Operations.SplitHalf

/-!
# `Zonotope.split`, over a floating-point scalar

CORA's `aux_splitOneDim`: `c1 = c - G(:,dim)/2`, `c2 = c + G(:,dim)/2` and the `dim`-th
generator halved in both. Halving is exact in a binary format, so only the two centres round;
each half stores the lower directed sum and pays the `centerResidual` into its error box, which
leaves the generator count unchanged as over ℝ. The halves cover `Z` only after that inflation.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two halves of `Z` along its `j`-th generator. -/
def Zonotope.split (Z : Zonotope (Vec 𝕋 n)) (j : Fin Z.h) : Zonotope (Vec 𝕋 n) ×
    Zonotope (Vec 𝕋 n) :=
  let g := fun i => half (Z.G j i)
  (Z.splitHalf j fun i => neg (g i), Z.splitHalf j g)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
