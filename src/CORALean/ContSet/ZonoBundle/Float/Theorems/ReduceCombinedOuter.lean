import CORALean.ContSet.ZonoBundle.Float.Operations.ReduceCombined
import CORALean.ContSet.ZonoBundle.Float.Theorems.EnclosingParallelotopeOuter

/-!
# `ZonoBundle.reduceCombined` encloses the bundle

`enclosingParallelotope_outer` at the selected basis, which holds at any basis.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.reduceCombined_outer (zB : ZonoBundle 𝕋 n) (hk : 0 < zB.k) :
    zB.construct ⊆ (zB.reduceCombined hk).construct :=
  ZonoBundle.enclosingParallelotope_outer zB hk _

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
