import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

/-!
# A sound bound on `|nominal S|`

Split out of `EvalPoly.lean` (issue #62): read again by
`Theorems/EvalPolyOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

/-- A sound bound on `|nominal S|`, entrywise: the centre plus every generator's
magnitude, since every monomial is at most `1` in absolute value. -/
def PolyZonotope.evalPolyBoundS (S : PolyZonotope 𝕋 n) : Vec 𝕋 n :=
  fun i => addUp (absolute (S.c i)) (radius S.G i)

end CORALean.Float
