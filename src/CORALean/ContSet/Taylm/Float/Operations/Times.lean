import CORALean.ContSet.Taylm.Float.Operations.PolyBounds
import CORALean.ContSet.Taylm.Real.Operations.Degree
import CORALean.ContSet.Interval.Float.Operations.MulLo
import CORALean.ContSet.Interval.Float.Operations.MulHi

/-!
# `Taylm.times`

The exact layer's product, each coefficient product enclosed by `mulDown` and `mulUp`, the
upper end stored and the width added to the remainder, for the kept and the dropped terms
alike; the dropped terms are then bounded at their stored values.
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

def Taylm.times (T₁ T₂ : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let N := max T₁.maxOrder T₂.maxOrder
  let P := T₁.terms.flatMap fun a => T₂.terms.map fun b => (a, b)
  let keep := P.filter fun p => Nat.ble (Real.Taylm.degree (p.1.2 + p.2.2)) N
  let drop := P.filter fun p => !Nat.ble (Real.Taylm.degree (p.1.2 + p.2.2)) N
  -- the rounding of the coefficient products, kept and dropped
  let errK := listSumUp (keep.map fun p => subUp (mulUp p.1.1 p.2.1) (mulDown p.1.1 p.2.1))
  let errD := listSumUp (drop.map fun p => subUp (mulUp p.1.1 p.2.1) (mulDown p.1.1 p.2.1))
  let D := Taylm.polyBounds (drop.map fun p => (mulUp p.1.1 p.2.1, p.1.2 + p.2.2))
  let P₁ := Taylm.polyBounds T₁.terms
  let P₂ := Taylm.polyBounds T₂.terms
  { terms := keep.map fun p => (mulUp p.1.1 p.2.1, p.1.2 + p.2.2)
    remInf := subDown (addDown (addDown (addDown (subDown D.1 errD)
      (Interval.mulLo P₁.1 P₁.2 T₂.remInf T₂.remSup))
      (Interval.mulLo P₂.1 P₂.2 T₁.remInf T₁.remSup))
      (Interval.mulLo T₁.remInf T₁.remSup T₂.remInf T₂.remSup)) errK
    remSup := addUp (addUp (addUp (addUp (addUp D.2 errD)
      (Interval.mulHi P₁.1 P₁.2 T₂.remInf T₂.remSup))
      (Interval.mulHi P₂.1 P₂.2 T₁.remInf T₁.remSup))
      (Interval.mulHi T₁.remInf T₁.remSup T₂.remInf T₂.remSup)) errK
    maxOrder := N }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
