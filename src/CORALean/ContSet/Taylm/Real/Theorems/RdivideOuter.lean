import CORALean.ContSet.Taylm.Real.Operations.Rdivide
import CORALean.ContSet.Taylm.Real.Theorems.InvOuter
import CORALean.ContSet.Taylm.Real.Theorems.TimesOuter

/-!
# `Taylm.rdivide` encloses the quotient

Under the inverse's condition on the denominator, `inv_outer` and `times_outer` compose: the
result encloses `f / g`.

[1, Eq. 9]: `T₁/T₂ = T₁·(1/T₂)` encloses `f/g`.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.rdivide_outer {T₁ T₂ : Taylm n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g)
    (hside : 0 < min T₂.constCoef T₂.bounds.1 ∨ max T₂.constCoef T₂.bounds.2 < 0) :
    (T₁.rdivide T₂).Encloses fun t => f t / g t := by
  simpa [Taylm.rdivide, div_eq_mul_inv] using Taylm.times_outer h₁ (Taylm.inv_outer h₂ hside)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
