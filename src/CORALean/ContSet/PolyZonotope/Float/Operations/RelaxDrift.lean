module

public import CORALean.ContSet.PolyZonotope.Real.Operations.EDrift
public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
public import CORALean.Global.Partition

@[expose] public section

/-!
# The drift's two reaches, over a floating-point scalar

Split out of `RelaxExpMid.lean` (issue #62): read again by
`Theorems/RelaxExpMidOuter.lean`, outside this file.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The drift's two reaches, read off the exponent matrix and so the exact
layer's own bracket. -/
def PolyZonotope.relaxDrift (pZ : PolyZonotope (Vec 𝕋 n))
    (part : Split (Fin pZ.h) into (Fin d) ⊕ (Fin 2)) (k₀ : Fin pZ.p) : ℕ × ℕ :=
  Real.PolyZonotope.eDrift pZ.E k₀ (part.right 0) (part.right 1)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
