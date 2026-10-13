module

public import CORALean.ContSet.Taylm.Real.Taylm

@[expose] public section

/-!
# `Taylm.plus`

CORA's `plus` of two models over the same variables: the term lists side by side and the
remainders added. CORA merges equal monomials afterwards (`priv_compress`); that changes
the list, not the polynomial, and is not done here. Not the Minkowski sum of the two range
sets: the variables are shared, which is why this is no `Plus` instance.

This is the addition of [1, Def. 2], `(P₁ + P₂, I₁ + I₂)`.

The sum of [2, Eq. 6], with the scalars through `smul`.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
* [2] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
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

def Taylm.plus (T₁ T₂ : Taylm n) : Taylm n :=
  ⟨T₁.terms ++ T₂.terms, T₁.remInf + T₂.remInf, T₁.remSup + T₂.remSup,
    max T₁.maxOrder T₂.maxOrder⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
