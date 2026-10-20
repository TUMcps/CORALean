module

public import CORALean.ContSet.ZonoBundle.Float.ZonoBundle

@[expose] public section

/-!
# `ZonoBundle.replace`, over a floating-point scalar

CORA's `zonoBundle`/`replace(zB, index, Z)`: the `index`-th zonotope is overwritten by `Z`, the
others kept and the count unchanged. Nothing is computed, so nothing rounds: each member
carries its own error box.

## Inputs
* `zB` – float zonotope bundle
* `index` – member to overwrite
* `Z` – replacement zonotope

## Output
* the bundle with that member replaced
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.replace (zB : ZonoBundle (Vec 𝕋 n)) (index : Fin zB.k) (Z : Zonotope (Vec 𝕋 n)) :
    ZonoBundle (Vec 𝕋 n) where
  k := zB.k
  Z := Function.update zB.Z index Z

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
