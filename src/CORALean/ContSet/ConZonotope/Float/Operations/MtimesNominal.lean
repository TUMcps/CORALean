module

public import CORALean.ContSet.ConZonotope.Float.ConZonotope
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# `ConZonotope.mtimesNominal`: a matrix applied to the stored numbers, with no error box

The matrix against the centre and the generators, each product rounded down, the constraints
untouched and the error box the point `0`. The set it describes is not `M cZ` — a rounded
product is a different number — but is within `mtimesNominalErr` of it at each coefficient
vector (`mtimesNominal_err`), which is all an inner approximation asks of it: the caller then
makes room for that distance in the set it maps, rather than the result absorbing it in a box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {m n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `M c` and `M G` rounded down, the rows of `cZ` and no error box. -/
def ConZonotope.mtimesNominal (M : Mat 𝕋 m n) (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) : ConZonotope
    𝕋 (Vec 𝕋 m) where
  h := cZ.h
  c := fun i => dotDown (M i) cZ.c
  G := fun j => mulVecDown M (cZ.G j)
  P := cZ.P
  E := Interval.point fun _ => zero

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
