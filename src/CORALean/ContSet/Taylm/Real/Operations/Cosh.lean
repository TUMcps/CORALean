module

public import CORALean.ContSet.Taylm.Real.Operations.Taylor
public import CORALean.ContSet.Taylm.Real.Operations.Mag

@[expose] public section

/-!
# `Taylm.cosh`

CORA's `cosh`: the expansion at the constant part; every derivative of `cosh` is `cosh` or
`sinh`, at most `cosh` of the magnitude.

The hyperbolic cosine of [1, Def. 3 (cosh)].

## Inputs
* `T` – Taylor model

## Output
* Taylor model of hyperbolic cosine of the argument

## References

* [1] [K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics,
      2003.](../../../../../../references/2003/makino-ijpam-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.cosh (T : Taylm n) : Taylm n :=
  T.taylor Real.cosh T.constCoef (Real.cosh T.mag)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
