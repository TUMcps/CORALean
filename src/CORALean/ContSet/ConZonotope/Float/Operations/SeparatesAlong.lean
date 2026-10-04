import CORALean.ContSet.ConZonotope.Float.Operations.SupportBound
import CORALean.ContSet.HPolytope.Float.Operations.RowLin

/-!
# `ConZonotope.separatesAlong`

Whether direction `a` separates two float constrained zonotopes: the first set's
`boundDot` in direction `a` lies strictly (`ltStrict`) below the negated
`boundDot` of the second in direction `-a`, its lower bound along `a`. Any `a`
may be asked; the check, not the direction, is what a `true` rests on.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `true` only when, in direction `a`, the first set's upper bound lies strictly
below the second set's lower bound. -/
def ConZonotope.separatesAlong (cZ₁ cZ₂ : ConZonotope 𝕋 n) (a : Vec 𝕋 n) : Bool :=
  ltStrict (cZ₁.boundDot (c := rowLin (fun (_ : Fin 1) => a) 0) a fun _ => rfl).val
    (neg (cZ₂.boundDot (c := rowLin (fun (_ : Fin 1) j => neg (a j)) 0) (fun j => neg (a j))
      fun _ => rfl).val)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
