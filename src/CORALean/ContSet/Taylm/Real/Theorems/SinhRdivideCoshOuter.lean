import CORALean.ContSet.Taylm.Real.Theorems.RdivideOuter
import CORALean.ContSet.Taylm.Real.Theorems.SinhOuter
import CORALean.ContSet.Taylm.Real.Theorems.CoshOuter

/-!
# `tanh` as `sinh / cosh`

[1, Eq. 29]: `tanh(T) = sinh(T)·(1/cosh(T))`, the models of `sinh` and `cosh` divided by `rdivide`.
Encloses `tanh ∘ f` whenever the denominator's model passes the inverse's condition; CORA's
`tanh` is this quotient of its own `sinh` and `cosh`.

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

theorem Taylm.sinh_rdivide_cosh_outer {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f)
    (hside : 0 < min T.cosh.constCoef T.cosh.bounds.1 ∨ max T.cosh.constCoef T.cosh.bounds.2 < 0) :
    (T.sinh.rdivide T.cosh).Encloses fun t => Real.tanh (f t) := by
  simpa only [Real.tanh_eq_sinh_div_cosh] using
    Taylm.rdivide_outer (Taylm.sinh_outer h) (Taylm.cosh_outer h) hside

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
