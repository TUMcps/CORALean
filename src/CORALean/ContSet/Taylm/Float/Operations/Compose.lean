import CORALean.ContSet.Taylm.Float.Operations.Sum
import CORALean.ContSet.Taylm.Float.Operations.Pow
import CORALean.ContSet.Taylm.Float.Operations.Smul
import CORALean.ContSet.Taylm.Float.Operations.Minus
import CORALean.ContSet.Taylm.Float.Operations.Const
import CORALean.ContSet.Taylm.Float.Operations.Plus

/-!
# Composing a polynomial with a Taylor model

`Σₖ [lo k, hi k] (T - c)ᵏ` up to `N`, plus `[-ρ, ρ]`: the exact layer's `compose` with each
coefficient known only to within an enclosure, which is all a float can know of `exp c / k!`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.compose (T : Taylm 𝕋 n) (c : 𝕋) (lo hi : ℕ → 𝕋) (N : ℕ) (ρ : 𝕋) : Taylm 𝕋 n :=
  (Taylm.sum fun k : Fin (N + 1) =>
    ((T.minus (Taylm.const n c T.maxOrder)).pow k).smul (lo k) (hi k)).plus ⟨[], neg ρ, ρ, 0⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
