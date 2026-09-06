import CORALean.ContSet.PolyZonotope.Float.Operations.RelaxDrift

/-!
# `relaxExpMid`'s centre shift, as stored

Split out of `RelaxExpMid.lean` (issue #62): read again by `relaxCentreMid` in
this directory and by `Theorems/RelaxExpMidOuter.lean`, both outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}

/-- The centre shift as stored: half the upward reach less half the downward
one, in copies of the relaxed generator, rounded down. -/
def PolyZonotope.relaxShiftMid (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : Vec 𝕋 n :=
  fun i => half (subDown (nsmulDown (PZ.relaxDrift part k₀).2 (PZ.G i (part.right 0)))
    (nsmulUp (PZ.relaxDrift part k₀).1 (PZ.G i (part.right 0))))

end CORALean.Float
