module

public import CORALean.ContSet.Taylm.Real.Operations.Inv

@[expose] public section

/-!
# `Taylm.rdivide`

CORA's `rdivide` of two models: the numerator times `priv_inverse` of the denominator, which is
the multiplicative inverse of [1, Def. 3 (inverse)] followed by the product of [1, Def. 2].

[2, Eq. 9] writes the same quotient, `T₁·(1/T₂)`.

## Inputs
* `T₁` – numerator
* `T₂` – denominator

## Output
* Taylor model of the quotient

## References

* [1] [K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion Methods".
      International Journal of Pure and Applied Mathematics,
      2003.](../../../../../../references/2003/makino-ijpam-taylor-models.md)
* [2] [M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.](../../../../../../references/2018/althoff-arch-taylor-models.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.rdivide (T₁ T₂ : Taylm n) : Taylm n := T₁.times T₂.inv

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
