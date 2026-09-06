import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxDrift

/-!
# `relaxExpMid`'s new independent column, as stored

Split out of `RelaxExpMid.lean` (issue #62): read again by
`Theorems/RelaxExpMidOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}

/-- The new independent column as stored: half of as many copies of the relaxed
generator as the bracket is wide, rounded down. -/
def PolyZonotope.relaxGenMid (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => half (nsmulDown ((PZ.relaxDrift part k₀).1 + (PZ.relaxDrift part k₀).2)
    (PZ.G i (part.right 0)))

end CORALean.Float
