import CORALean.ContSet.Taylm.Real.Theorems.RdivideOuter
import CORALean.ContSet.Taylm.Real.Theorems.SinOuter
import CORALean.ContSet.Taylm.Real.Theorems.CosOuter

/-!
# `tan` as `sin / cos`

[1, Eq. 26]: `tan(T) = sin(T)·(1/cos(T))`, the models of `sin` and `cos` divided by `rdivide`.
Encloses `tan ∘ f` whenever the denominator's model passes the inverse's condition; CORA's
`tan` is this quotient of its own `sin` and `cos`.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.sin_rdivide_cos_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hside : 0 < min T.cos.constCoef T.cos.bounds.1 ∨ max T.cos.constCoef T.cos.bounds.2 < 0) :
    (T.sin.rdivide T.cos).Encloses fun t => Real.tan (f t) := by
  simpa only [Real.tan_eq_sin_div_cos] using
    Taylm.rdivide_outer (Taylm.sin_outer h) (Taylm.cos_outer h) hside

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
