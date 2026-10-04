import CORALean.ContSet.Interval.Real.Operations.MulHi
import CORALean.ContSet.Interval.Real.Operations.MulLo

/-!
# Intervals: multiplication by an interval matrix

The product of two interval matrices, entrywise: entry `(i, j)` is the sum over
`k` of the corner hull of `A`'s `(i, k)` interval against `B`'s `(k, j)` one,
exactly `mtimesIntervalMat`'s row sum with a second matrix index riding along.

**Breaks the `mtimes*` family on purpose**: every `mtimes` in the tree ends in a
set of vectors, and this one ends in a set of matrices.

[1, Eq. 16]: `([X][Y])ᵢⱼ = Σₖ [X]ᵢₖ[Y]ₖⱼ`.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n p : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.matMul (A : Interval (Mat ℝ m n)) (B : Interval (Mat ℝ n p)) :
    Interval (Mat ℝ m p) where
  inf := fun i j => ∑ k, Interval.mulLo (A.inf i k) (A.sup i k) (B.inf k j) (B.sup k j)
  sup := fun i j => ∑ k, Interval.mulHi (A.inf i k) (A.sup i k) (B.inf k j) (B.sup k j)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
