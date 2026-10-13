module

public import CORALean.ContSet.PolyZonotope.Float.PolyZonotope

@[expose] public section

/-!
# `PolyZonotope.maxExp`, over a floating-point scalar

The largest exponent factor `k` carries over the dependent generators: the exact layer's count, on
the stored exponent matrix, so the two agree.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.maxExp (pZ : PolyZonotope (Vec 𝕋 n)) (k : Fin pZ.p) : ℕ :=
  Finset.univ.sup fun i => pZ.E k i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
