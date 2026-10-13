import CORALean.ContSet.Taylm.Float.Operations.Compose
import CORALean.ContSet.Taylm.Float.Operations.TrigCoef
import CORALean.ContSet.Taylm.Float.Operations.UnitRemainder

/-!
# `Taylm.sin`

The exact layer's `sin` with every number enclosed: the expansion at the constant part `c` to
`maxOrder`, the coefficients `sin⁽ᵏ⁾(c) / k!` by `trigCoef`, and the remainder `unitRemainder`,
every derivative of `sin` being at most one in magnitude. `p` is the number of halvings of the
sine and cosine (`Global/Float/SinCos`).
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.sin (p : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let N := T.maxOrder
  let c := T.constCoef
  let ρ := T.unitRemainder
  T.compose c (fun k => (Taylm.trigCoef p c k).1.1) (fun k => (Taylm.trigCoef p c k).1.2) N ρ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
