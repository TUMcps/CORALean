module

public import CORALean.ContSet.Taylm.Real.Operations.Taylor
public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

/-!
# `Taylm.sin`

CORA's `sin`: the expansion at the constant part, every derivative of `sin` bounded by
`1`.

The sine of [1, Def. 3 (sin)], whose remainder term `J` is a derivative of `sin`, at most one.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.sin (T : Taylm n) : Taylm n :=
  T.taylor Real.sin T.constCoef 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
