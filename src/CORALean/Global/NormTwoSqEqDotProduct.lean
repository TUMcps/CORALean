import CORALean.Global.Tensor
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The squared Euclidean norm is the dot product with itself

`‖x‖₂² = x ⬝ᵥ x` on `Vec ℝ n` read in `ℓ₂`, which carries the Euclidean norm only through
`toLp 2`: the bridge `[1, App. B]`'s rounding by `B₂` needs from `Vec ℝ n`'s supremum norm.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open WithLp Matrix

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem norm_two_sq_eq_dotProduct (v : Fin n → ℝ) : ‖toLp 2 v‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp [dotProduct, sq]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
