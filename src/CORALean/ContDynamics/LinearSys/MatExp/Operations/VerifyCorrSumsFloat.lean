module

public import CORALean.ContSet.Interval.Float.Operations.MaterialiseMat

@[expose] public section

/-!
# `MatExp.verifyCorrSumsFloat`, the sums of CORA's `aux_intmat`

CORA's `aux_intmat` accumulates the terms of `F` and `G` split by sign, `Asum_neg += factor*Apos`
and `Asum_pos += factor*Aneg`, from the first term up. Here the same over boxes: the lower ends,
clamped at `0` from above, summed with every addition rounded down; the upper ends, clamped at `0`
from below, summed rounded up, each from `zero` and in the order of the list.

## Inputs
* `T` – float term boxes, in order

## Output
* the box of the lower and upper sums
-/

-- Authors:       Claude Opus 5.5
-- Written:       17-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sums of the terms in their order: lower ends down, upper ends up, from `zero`. -/
def MatExp.verifyCorrSumsFloat (T : List (Interval (Mat 𝕋 n n))) : Interval (Mat 𝕋 n n) :=
  (⟨fun j k => T.foldl (fun acc t => addDown acc (minimum (t.inf j k) zero)) zero,
    fun j k => T.foldl (fun acc t => addUp acc (maximum (t.sup j k) zero)) zero⟩ :
      Interval (Mat 𝕋 n n)).materialiseMat

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
