module

public import CORALean.ContSet.Taylm.Float.Operations.Compose
public import CORALean.ContSet.Taylm.Float.Operations.TrigCoef
public import CORALean.ContSet.Taylm.Float.Operations.UnitRemainder

@[expose] public section

/-!
# `Taylm.sin`

The exact layer's `sin` with every number enclosed: the expansion at the constant part `c` to
`maxOrder`, the coefficients `sin⁽ᵏ⁾(c) / k!` by `trigCoef`, and the remainder `unitRemainder`,
every derivative of `sin` being at most one in magnitude. `p` is the number of halvings of the
sine and cosine (`Global/Float/SinCos`).

## Inputs
* `p` – precision of the halvings
* `T` – Taylor model

## Output
* Taylor model of sine of the argument
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.sin (p : ℕ) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let N := T.maxOrder
  let c := T.constCoef
  let ρ := T.unitRemainder
  T.compose c (fun k => (Taylm.trigCoef p c k).1.inf) (fun k => (Taylm.trigCoef p c k).1.sup) N ρ

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
