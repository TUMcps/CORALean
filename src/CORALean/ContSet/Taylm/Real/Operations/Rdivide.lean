import CORALean.ContSet.Taylm.Real.Operations.Inv
import CORALean.ContSet.Taylm.Real.Operations.Times

/-!
# `Taylm.rdivide`

CORA's `rdivide` of two models: the numerator times `priv_inverse` of the denominator, which is
the multiplicative inverse of [1, Def. 3 (inverse)] followed by the product of [1, Def. 2].

[2, Eq. 9] writes the same quotient, `T₁·(1/T₂)`.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
* [2] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.rdivide (T₁ T₂ : Taylm n) : Taylm n := T₁.times T₂.inv

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
