module

public import CORALean.ContSet.Taylm.Real.Operations.Taylor
public import CORALean.ContSet.Taylm.Real.Operations.Basic
public import CORALean.ContSet.Taylm.Real.Operations.Mag
public import CORALean.Global.ElementaryDerivBounds

@[expose] public section

/-!
# `Taylm.atan`

CORA's `atan`: the expansion at the constant part. `atan⁽ᴺ⁺¹⁾ x` is `atanPoly N x` times
`(1 + x²)⁻⁽ᴺ⁺¹⁾`, the second factor at most one, the first bounded by `atanDom N` at the
magnitude. No domain condition.

A Taylor model of `arctan ∘ f` as [1, Def. 3 (arctan)] asks, but expanded at `c_f` directly
rather than through the source's addition formula, which needs `1 + c_f·f > 0`
(`AtanShift`).

## Inputs
* `T` – Taylor model

## Output
* Taylor model of arctan of the argument

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.atan (T : Taylm n) : Taylm n :=
  T.taylor Real.arctan T.constCoef ((atanDom T.maxOrder).eval T.mag)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
