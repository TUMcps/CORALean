module

public import CORALean.ContSet.Taylm.Float.Operations.AccumTerms

@[expose] public section

/-!
# `Taylm.plusMerged`

The sum of two Taylor models over the same variables as CORA.cpp's `Taylm::plus` computes it:
the terms of the second added one by one into the sorted terms of the first
(`Taylm.accumTerms`, equal monomials merged), the remainders added. What the merged sums cost
in rounding goes to the error box, with the boxes' sum. The order is the first model's.

## Inputs
* `T₁` – first summand
* `T₂` – second summand

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

def Taylm.plusMerged (T₁ T₂ : Taylm 𝕋 n) : Taylm 𝕋 n :=
  let S := Taylm.accumTerms T₁.terms T₂.terms
  { terms := S.1
    rem := ⟨addDown T₁.rem.inf T₂.rem.inf, addUp T₁.rem.sup T₂.rem.sup⟩
    I_error := ⟨subDown (addDown T₁.I_error.inf T₂.I_error.inf) S.2,
      addUp (addUp T₁.I_error.sup T₂.I_error.sup) S.2⟩
    maxOrder := T₁.maxOrder }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
