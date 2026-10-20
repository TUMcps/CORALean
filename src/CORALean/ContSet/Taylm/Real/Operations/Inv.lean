module

public import CORALean.ContSet.Taylm.Real.Operations.Taylor

@[expose] public section

/-!
# `Taylm.inv`

The multiplicative inverse of [1, Def. 3 (inverse)], eq. (2.6): the expansion of `1/x` at the
constant part `c_f`, the Lagrange term `(-1)ᴺ⁺¹ (N+1)! / ξᴺ⁺²` largest in magnitude where the
hull of the center and the range comes closest to zero. The source's condition, `0` outside the
range, is the hull lying on one side of zero; `m` is then its distance from zero. CORA's
`priv_inverse` (behind `rdivide` and `mrdivide`) is the same expansion.

## Inputs
* `T` – Taylor model

## Output
* Taylor model of the reciprocal

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.inv (T : Taylm n) : Taylm n :=
  let c := T.constCoef
  -- the hull of the center and the range, and its distance from zero
  let m := max (min c T.bounds.inf) (-max c T.bounds.sup)
  T.taylor (fun x => x⁻¹) c (((T.maxOrder + 1).factorial : ℝ) / m ^ (T.maxOrder + 2))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
