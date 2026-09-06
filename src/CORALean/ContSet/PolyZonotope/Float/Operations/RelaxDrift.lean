import CORALean.ContSet.PolyZonotope.Real.Operations.EDrift
import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.Global.Partition

/-!
# The drift's two reaches, over a floating-point scalar

Split out of `RelaxExpMid.lean` (issue #62): read again by
`Theorems/RelaxExpMidOuter.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}

/-- The drift's two reaches, read off the exponent matrix and so the exact
layer's own bracket. -/
def PolyZonotope.relaxDrift (PZ : PolyZonotope 𝕋 n)
    (part : Split (Fin PZ.h) into (Fin d) and (Fin 2)) (k₀ : Fin PZ.p) : ℕ × ℕ :=
  Real.PolyZonotope.eDrift PZ.E k₀ (part.right 0) (part.right 1)

end CORALean.Float
