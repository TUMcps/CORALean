module

public import CORALean.ContSet.ZonoBundle.Float.Operations.ReduceCombined
public import CORALean.ContSet.ZonoBundle.Float.Theorems.EnclosingParallelotopeOuter

@[expose] public section

/-!
# `ZonoBundle.reduceCombined` encloses the bundle

`enclosingParallelotope_outer` at the selected basis, which holds at any basis.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.reduceCombined_outer (zB : ZonoBundle (Vec 𝕋 n)) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.reduceCombined hk).construct :=
  ZonoBundle.enclosingParallelotope_outer zB hk _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
