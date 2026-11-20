module

public import CORALean.ContSet.Taylm.Float.Operations.Basic
public import CORALean.ContSet.Taylm.Float.Operations.TimesZeroInf
public import CORALean.Global.Float.ListSum

@[expose] public section

/-!
# `Taylm.scale`

A Taylor model times a number as CORA.cpp's `Taylm::times(double)` computes it: every
coefficient times the number, the remainder by the interval product with `[s, s]`
(`Taylm.timesZeroInf`), the error box in the remainder first. The coefficient products are stored
rounded up; their widths go to the error box.

## Inputs
* `T` – Taylor model
* `s` – number

## Output
* Taylor model of the product
-/

-- Authors:       Claude Opus 5.5
-- Written:       20-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.scale (T : Taylm 𝕋 n) (s : 𝕋) : Taylm 𝕋 n :=
  -- what storing the upper rounding of each coefficient product costs
  let err := listSumUp (T.terms.map fun a => subUp (mulUp a.1 s) (mulDown a.1 s))
  { terms := T.terms.map fun a => (mulUp a.1 s, a.2)
    rem := Taylm.timesZeroInf T.absorbRounding.rem ⟨s, s⟩
    I_error := ⟨neg err, err⟩
    maxOrder := T.maxOrder }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
