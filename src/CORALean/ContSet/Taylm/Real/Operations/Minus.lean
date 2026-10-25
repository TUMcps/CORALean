module

public import CORALean.ContSet.Taylm.Real.Operations.Basic

@[expose] public section

/-!
# `Taylm.minus`

CORA's `minus`, as `plus` of the negation; CORA subtracts the remainders, which is the
same interval.

The difference of [1, Eq. 7], with the scalars through `smul`.

## Inputs
* `T₁` – first model
* `T₂` – second model

## Output
* Taylor model of the difference

## References

* [1] M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.minus (T₁ T₂ : Taylm n) : Taylm n := T₁.plus T₂.uminus

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
