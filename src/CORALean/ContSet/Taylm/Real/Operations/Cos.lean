module

public import CORALean.ContSet.Taylm.Real.Operations.Taylor

@[expose] public section

/-!
# `Taylm.cos`

CORA's `cos`: the expansion at the constant part, every derivative of `cos` bounded by
`1`.

The cosine of [1, Def. 3 (cos)], whose remainder term `J` is a derivative of `cos`, at most one.

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

noncomputable def Taylm.cos (T : Taylm n) : Taylm n :=
  T.taylor Real.cos T.constCoef 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
