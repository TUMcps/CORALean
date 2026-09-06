import CORALean.ContSet.PolyZonotope.Real.Operations.EDiff
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.Global.Partition

/-!
# `ξ_E`, over a floating-point scalar

Split out of `RelaxExp.lean` (issue #62): read again by `relaxExpEven` in this
directory and by `Theorems/RelaxExpOuter.lean` and
`Theorems/RelaxExpEvenOuter.lean`, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `ξ_E`, read off the exponent matrix and so the exact layer's own width. -/
def PolyZonotope.relaxWidth (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : ℕ :=
  Real.PolyZonotope.eDiff (PZ.E k₀ (part.right 0)) (PZ.E k₀ (part.right 1))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
