import CORALean.ContSet.Taylm.Real.Operations.MulTerms
import CORALean.ContSet.Taylm.Real.Operations.PolyBounds
import CORALean.ContSet.Interval.Real.Operations.MulLo
import CORALean.ContSet.Interval.Real.Operations.MulHi

/-!
# `Taylm.times`

CORA's `times` of two models (`aux_s_times_tt`): the product polynomial,
truncated at the larger order, the dropped terms bounded into the remainder
(`priv_compress`), and the three cross terms `B(p₁)·I₂ + B(p₂)·I₁ + I₁·I₂` added as
interval products, `B` being `polyBounds`. CORA's tolerance, moving coefficients under
`1e-8` into the remainder, is a precision choice and not done.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.times (T₁ T₂ : Taylm n) : Taylm n :=
  let N := max T₁.maxOrder T₂.maxOrder
  let L := Taylm.mulTerms T₁.terms T₂.terms
  -- the terms above the order, bounded rather than kept
  let D := Taylm.polyBounds (L.filter fun a => !Nat.ble (Taylm.degree a.2) N)
  let P₁ := Taylm.polyBounds T₁.terms
  let P₂ := Taylm.polyBounds T₂.terms
  { terms := L.filter fun a => Nat.ble (Taylm.degree a.2) N
    remInf := D.1 + Interval.mulLo P₁.1 P₁.2 T₂.remInf T₂.remSup
      + Interval.mulLo P₂.1 P₂.2 T₁.remInf T₁.remSup
      + Interval.mulLo T₁.remInf T₁.remSup T₂.remInf T₂.remSup
    remSup := D.2 + Interval.mulHi P₁.1 P₁.2 T₂.remInf T₂.remSup
      + Interval.mulHi P₂.1 P₂.2 T₁.remInf T₁.remSup
      + Interval.mulHi T₁.remInf T₁.remSup T₂.remInf T₂.remSup
    maxOrder := N }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
