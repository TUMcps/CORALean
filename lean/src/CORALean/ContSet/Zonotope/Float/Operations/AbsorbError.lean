import CORALean.ContSet.Zonotope.Float.Zonotope

/-!
# `Zonotope.absorbError`

Trade the box for `n` generators about its own midpoint. Over ℝ this moves
nothing; here the shifted centre must be stored as a float, so the box is left
holding what that rounding still owes rather than becoming `[0, 0]`.

`shiftDown`, `shiftUp` and `errorRadius` are shared with `reduceAndAbsorbBy`,
which does this and a reduction in one pass.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- The box midpoint added to the centre, rounded each way. The exact midpoint
need not be a float — `[5, 6]` gives 5.5 — so the gap between the two roundings
is what `absorbError` leaves behind. -/
def Zonotope.shiftDown (Z : Zonotope 𝕋 n) : Vec 𝕋 n :=
  fun i => addDown (Z.c i) (half (addDown (Z.E.inf i) (Z.E.sup i)))

def Zonotope.shiftUp (Z : Zonotope 𝕋 n) : Vec 𝕋 n :=
  fun i => addUp (Z.c i) (half (addUp (Z.E.inf i) (Z.E.sup i)))

/-- The box radius, rounded up; halving is exact, so only the difference rounds. -/
def Zonotope.errorRadius (Z : Zonotope 𝕋 n) : Vec 𝕋 n :=
  fun i => half (subUp (Z.E.sup i) (Z.E.inf i))

def Zonotope.absorbError (Z : Zonotope 𝕋 n) : Zonotope 𝕋 n where
  h := Z.h + n
  c := Z.shiftDown
  G := fun i => Fin.append (Z.G i) (diagonalBlock Z.errorRadius i)
  E := Interval.residual Z.shiftDown Z.shiftUp Z.shiftDown

end CORALean.Float
