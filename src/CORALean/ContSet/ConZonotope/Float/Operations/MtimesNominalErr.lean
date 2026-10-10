import CORALean.ContSet.ConZonotope.Float.ConZonotope

/-!
# `ConZonotope.mtimesNominalErr`: how far `mtimesNominal` can be from the exact product

At every coefficient vector in the unit box, in each coordinate: the centre's rounding, the
gap between the rounded-up and rounded-down dot product, plus the generators' rounding summed
over a row, `radius (matMulDiff M G)`, all rounded up.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The distance bound of `M c` and `M G` rounded, per coordinate, rounded up. -/
def ConZonotope.mtimesNominalErr (M : Mat 𝕋 m n) (cZ : ConZonotope 𝕋 n) : Vec 𝕋 m :=
  fun i => addUp (subUp (dotUp (M i) cZ.c) (dotDown (M i) cZ.c))
    (radius (matMulDiff M cZ.G) i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
