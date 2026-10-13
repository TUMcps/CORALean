import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.Global.Partition

/-!
# `ξ_E` summed over every factor, over a floating-point scalar

Split out of `RelaxExpMulti.lean` (issue #62): read again by
`Theorems/RelaxExpMultiOuter.lean`, outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ξ_E` summed over every factor, read off the exponent matrix and so the
exact layer's own width. -/
def PolyZonotope.relaxWidthMulti (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) : ℕ :=
  ∑ k, Real.PolyZonotope.eDiff (pZ.E k (part.right 0)) (pZ.E k (part.right 1))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
