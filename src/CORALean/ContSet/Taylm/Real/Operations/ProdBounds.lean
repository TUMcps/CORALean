module

public import CORALean.ContSet.Interval.Real.Operations.Basic

@[expose] public section

/-!
# The product of a list of intervals

Interval multiplication folded from the right, starting at `[1, 1]`: how [1, Eq. 12] bounds a
monomial from its factors' powers.

## Inputs
* none

## Output
* product of the listed intervals

## References

* [1] M. Althoff, D. Grebenyuk and N. Kochdumper. "Implementation of Taylor Models in CORA 2018".
      ARCH18. 5th International Workshop on Applied Verification of Continuous and Hybrid Systems,
      2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.prodBounds : List (Interval ℝ) → Interval ℝ
  | [] => ⟨1, 1⟩
  | a :: L => ⟨Interval.mulLo a.inf a.sup (Taylm.prodBounds L).inf (Taylm.prodBounds L).sup,
      Interval.mulHi a.inf a.sup (Taylm.prodBounds L).inf (Taylm.prodBounds L).sup⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
