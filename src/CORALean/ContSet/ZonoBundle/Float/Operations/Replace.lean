import CORALean.ContSet.ZonoBundle.Float.ZonoBundle

/-!
# `ZonoBundle.replace`, over a floating-point scalar

CORA's `zonoBundle`/`replace(zB, index, Z)`: the `index`-th zonotope is overwritten by `Z`, the
others kept and the count unchanged. Nothing is computed, so nothing rounds: each member
carries its own error box.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.replace (zB : ZonoBundle 𝕋 n) (index : Fin zB.k) (Z : Zonotope 𝕋 n) :
    ZonoBundle 𝕋 n where
  k := zB.k
  Z := Function.update zB.Z index Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
