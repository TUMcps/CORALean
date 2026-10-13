import CORALean.ContSet.PolyZonotope.Float.PolyZonotope
import CORALean.ContSet.Zonotope.Float.Operations.CubContractUp
import CORALean.ContSet.Zonotope.Real.Operations.CubIdx

/-!
# `PolyZonotope.cubMapGUp`

The generators of `PolyZonotope.cubMap`, rounded up: one per ordered triple `(a, b, c)` of extended
generators `[c, G]` (`Real.Zonotope.cubIdx`), the cubic contraction `Σₖ g_a(k) (g_bᵀ T{i,k} g_c)`
through `Zonotope.cubContractUp`. The monomial of the triple is the product of the three, so the
exponent column is the sum of theirs.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.cubMapGUp (T : Fin m → Fin n → Mat 𝕋 n n) (pZ : PolyZonotope (Vec 𝕋 n)) :
    Fin m → Fin ((pZ.h + 1) * (pZ.h + 1) * (pZ.h + 1)) → 𝕋 :=
  fun i l =>
    -- `[c, G]`
    let Zext : Fin (pZ.h + 1) → Vec 𝕋 n := Fin.cons pZ.c pZ.G
    let t := Real.Zonotope.cubIdx (pZ.h + 1) (pZ.h + 1) (pZ.h + 1) l
    Zonotope.cubContractUp T (Zext t.1.1) (Zext t.1.2) (Zext t.2) i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
