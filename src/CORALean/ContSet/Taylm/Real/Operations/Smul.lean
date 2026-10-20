module

public import CORALean.ContSet.Taylm.Real.Taylm
public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# `Taylm.smul`

CORA's `times` and `mtimes` by a number (`aux_s_times_td`): the coefficients and the
remainder scaled. The remainder is the interval product, so a negative factor swaps its
ends.

The scalar factors of [1, Eq. 6] and [1, Eq. 7], `(αP, α[I])`.

## Inputs
* `a` – scalar
* `T` – Taylor model

## Output
* Taylor model scaled by the scalar

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.smul (a : ℝ) (T : Taylm n) : Taylm n :=
  ⟨T.terms.map fun b => (a * b.1, b.2), ⟨Interval.mulLo a a T.rem.inf T.rem.sup,
    Interval.mulHi a a T.rem.inf T.rem.sup⟩, T.maxOrder⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
