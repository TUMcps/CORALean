module

public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_Interval
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Zonotope.Float.Operations.QuadMapTri

@[expose] public section

/-!
# `Interval.quadMapCora`

CORA's `@interval/quadMap` as CORA.cpp computes it: the box of the quadratic map of the box's
zonotope, where the zonotope is mapped by CORA's own `quadMap`, `Zonotope.quadMapTri` (the
squares, then the lower triangle of `M + Mᵀ`). `Interval.quadMap` goes through `Zonotope.quadMap`,
a polynomial zonotope, and is a wider box.

## Inputs
* `Q` – family of quadratic form matrices
* `I` – interval box

## Output
* box enclosing the quadratic map of `I`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       22-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.quadMapCora (Q : Fin m → Mat 𝕋 n n) (I : Interval (Vec 𝕋 n)) :
    Interval (Vec 𝕋 m) :=
  (Zonotope.quadMapTri Q I.zonotope).interval

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
