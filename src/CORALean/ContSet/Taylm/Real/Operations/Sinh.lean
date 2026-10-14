module

public import CORALean.ContSet.Taylm.Real.Operations.Taylor
public import CORALean.ContSet.Taylm.Real.Operations.Mag

@[expose] public section

/-!
# `Taylm.sinh`

CORA's `sinh`: the expansion at the constant part; every derivative of `sinh` is `sinh` or
`cosh`, at most `cosh` of the magnitude.

The hyperbolic sine of [1, Def. 3 (sinh)].

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

noncomputable def Taylm.sinh (T : Taylm n) : Taylm n :=
  T.taylor Real.sinh T.constCoef (Real.cosh T.mag)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
