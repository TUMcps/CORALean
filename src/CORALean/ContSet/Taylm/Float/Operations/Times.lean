module

public import CORALean.ContSet.Taylm.Float.Operations.Basic

@[expose] public section

/-!
# `Taylm.times`

The exact layer's product of the two operands with their error boxes absorbed into their
remainders first (`Taylm.absorbRounding`), since the cross terms multiply the remainders. Each
coefficient product is enclosed by `mulDown` and `mulUp` and the upper end stored; the width of a
kept term goes to the error box, the width of a dropped one to the remainder, with the dropped
terms bounded at their stored values and the cross terms of the remainders.

## Inputs
* `T₁` – first factor
* `T₂` – second factor

## Output
* Taylor model of the product
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.times (T₁ T₂ : Taylm 𝕋 n) : Taylm 𝕋 n :=
  -- the operands' remainders with their boxes in them
  let A := T₁.absorbRounding
  let B := T₂.absorbRounding
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
    rem := ⟨addDown (addDown (addDown (subDown D.inf errD)
      (Interval.mulLo P₁.inf P₁.sup B.rem.inf B.rem.sup))
      (Interval.mulLo P₂.inf P₂.sup A.rem.inf A.rem.sup))
      (Interval.mulLo A.rem.inf A.rem.sup B.rem.inf B.rem.sup),
      addUp (addUp (addUp (addUp D.sup errD)
      (Interval.mulHi P₁.inf P₁.sup B.rem.inf B.rem.sup))
      (Interval.mulHi P₂.inf P₂.sup A.rem.inf A.rem.sup))
      (Interval.mulHi A.rem.inf A.rem.sup B.rem.inf B.rem.sup)⟩
    I_error := ⟨neg errK, errK⟩
    maxOrder := N }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
