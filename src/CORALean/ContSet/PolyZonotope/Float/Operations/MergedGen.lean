import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.Global.Partition

/-!
# The two merged generators, as stored

Split out of `RelaxExp.lean` (issue #62): every relaxation shares this column —
`relaxExpEven`, `relaxExpMulti` and `relaxExpMid` all reuse it rather than
restating it, and so does `Theorems/MergedGenGap.lean`, the gap fact common to
all of them.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two merged generators as stored: their sum, rounded down. -/
def PolyZonotope.mergedGen (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) ⊕ (Fin 2)) : Vec 𝕋 n :=
  fun i => addDown (PZ.G i (part.right 1)) (PZ.G i (part.right 0))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
