import CORALean.ContSet.Interval.Real.Interval

/-!
# `Interval.or`

CORA's `@interval/or` at two intervals: the coordinatewise hull `[min inf, max sup]`.
CORA returns the other operand when one is empty; the definition does not branch, and
`Theorems/OrOuter.lean` says what that costs.

[1, Eq. 1]: the interval hull `[min(x̲, y̲), max(x̅, y̅)]`, which is the union when the two meet.

## References

* [1] M. Althoff and D. Grebenyuk. "Implementation of Interval Arithmetic in CORA 2016". In
      Proc. of the 3rd International Workshop on Applied Verification for Continuous and Hybrid
      Systems (ARCH16), EPiC Series in Computing, vol. 43, pp. 91-105, 2017.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Entrywise

variable {α ι : Type} [AddCommGroup α] [Module ℝ α] [Entrywise α ι]


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.or (I₁ I₂ : Interval α) : Interval α where
  inf := ofEntry fun i => min (entry I₁.inf i) (entry I₂.inf i)
  sup := ofEntry fun i => max (entry I₁.sup i) (entry I₂.sup i)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
