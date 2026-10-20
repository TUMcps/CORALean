module

public import Mathlib.Data.Real.Basic
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# The coordinate of largest radius

Line 11 of [1, Alg. 1]: the coordinate along which a box is widest, the first of several; `none`
when the box has no coordinates.

## Inputs
* `B` – box

## Output
* index of the widest coordinate, if any

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.widestCoord (B : Fin n → Interval ℝ) : Option (Fin n) :=
  (List.finRange n).foldl (fun best k => match best with
    | none => some k
    | some j => if (B j).sup - (B j).inf < (B k).sup - (B k).inf then some k else some j) none

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
