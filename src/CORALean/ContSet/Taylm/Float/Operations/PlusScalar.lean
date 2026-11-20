module

public import CORALean.ContSet.Taylm.Float.Operations.AccumTerm

@[expose] public section

/-!
# `Taylm.plusScalar`

A Taylor model plus a number as CORA.cpp's `Taylm::plus(double)` computes it: the number added
into the constant term (`Taylm.accumTerm` at the zero exponents), the remainder unchanged; the
rounding of that sum goes to the error box.

## Inputs
* `T` – Taylor model
* `s` – number

## Output
* Taylor model of the sum
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

def Taylm.plusScalar (T : Taylm 𝕋 n) (s : 𝕋) : Taylm 𝕋 n :=
  let S := Taylm.accumTerm T.terms s 0
  { T with terms := S.1, I_error := ⟨subDown T.I_error.inf S.2, addUp T.I_error.sup S.2⟩ }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
