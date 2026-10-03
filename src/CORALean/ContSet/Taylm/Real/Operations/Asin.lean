import CORALean.ContSet.Taylm.Real.Operations.Taylor
import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
import CORALean.ContSet.Taylm.Real.Operations.Mag
import CORALean.Global.ElementaryDerivBounds

/-!
# `Taylm.asin`

CORA's `asin`: the expansion at the constant part. `asin⁽ᴺ⁺¹⁾ x` is `asinPoly N x` times
`(1 - x²)⁻⁽²ᴺ⁺¹⁾ᐟ²`, bounded by `asinDom N` at the magnitude `m` and `(1 - m²)⁻⁽²ᴺ⁺¹⁾ᐟ²`,
finite below one, the domain `AsinOuter` assumes.

A Taylor model of `arcsin ∘ f` as [1, Def. 3 (arcsin)] asks, but expanded at `c_f` directly
rather than through the source's addition formula, which fails on wide ranges
(`ArcsinShiftCounterexample`).

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.asin (T : Taylm n) : Taylm n :=
  T.taylor Real.arcsin T.constCoef
    ((asinDom T.maxOrder).eval T.mag * ((√(1 - T.mag ^ 2))⁻¹) ^ (2 * T.maxOrder + 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
