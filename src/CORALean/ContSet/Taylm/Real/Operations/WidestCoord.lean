import Mathlib.Data.Real.Basic
import Mathlib.Data.List.FinRange

/-!
# The coordinate of largest radius

Line 11 of [1, Alg. 1]: the coordinate along which a box is widest, the first of several; `none`
when the box has no coordinates.

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


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.widestCoord (B : Fin n → ℝ × ℝ) : Option (Fin n) :=
  (List.finRange n).foldl (fun best k => match best with
    | none => some k
    | some j => if (B j).2 - (B j).1 < (B k).2 - (B k).1 then some k else some j) none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
