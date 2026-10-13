import CORALean.ContSet.Taylm.Real.Operations.Plus
import Mathlib.Tactic.Linarith

/-!
# `Taylm.plus` encloses the sum

Of the two functions, at the same point of the box: the shared variables are what makes the
sum exact on the polynomials.

The sum of [1, Def. 2] is a Taylor model of `f + g`.

[2, Eq. 6]: with `smul_outer`, `αT₁ + βT₂` encloses `αf + βg`.

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.plus_outer {T₁ T₂ : Taylm n} {f g : Vec ℝ n → ℝ} (h₁ : T₁.Encloses f)
    (h₂ : T₂.Encloses g) : (T₁.plus T₂).Encloses fun t => f t + g t := by -- --- PROOF ---
  intro t ht
  have := h₁ t ht
  have := h₂ t ht
  simp only [Taylm.plus, Taylm.poly, Taylm.polyOf_append] at *
  constructor <;> linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
