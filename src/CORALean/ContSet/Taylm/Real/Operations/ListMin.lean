module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The least value over a list

The lower end of the union of [1, Alg. 1]'s intervals (line 30); `0` for the empty list, which the
algorithm never has.

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

noncomputable def Taylm.listMin {α : Type} (f : α → ℝ) : List α → ℝ
  | [] => 0
  | [a] => f a
  | a :: b :: l => min (f a) (Taylm.listMin f (b :: l))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
