import CORALean.ContSet.Interval.Real.Operations.MulLo
import CORALean.ContSet.Interval.Real.Operations.MulHi

/-!
# The product of a list of intervals

Interval multiplication folded from the right, starting at `[1, 1]`: how [1, Eq. 12] bounds a
monomial from its factors' powers.

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


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.prodBounds : List (ℝ × ℝ) → ℝ × ℝ
  | [] => (1, 1)
  | a :: L => (Interval.mulLo a.1 a.2 (Taylm.prodBounds L).1 (Taylm.prodBounds L).2,
      Interval.mulHi a.1 a.2 (Taylm.prodBounds L).1 (Taylm.prodBounds L).2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
