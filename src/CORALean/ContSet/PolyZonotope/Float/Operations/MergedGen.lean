module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# The two merged generators, as stored

Split out of `RelaxExp.lean` (issue #62): every relaxation shares this column —
`relaxExpEven`, `relaxExpMulti` and `relaxExpMid` all reuse it rather than
restating it, and so does `Theorems/MergedGenGap.lean`, the gap fact common to
all of them.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two merged generators as stored: their sum, rounded down. -/
def PolyZonotope.mergedGen (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) : Vec 𝕋 n :=
  fun i => addDown (pZ.G (part.right 1) i) (pZ.G (part.right 0) i)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
