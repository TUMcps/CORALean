module

public import CORALean.ContSet.Taylm.Real.Operations.HalveBox
public import CORALean.ContSet.Taylm.Real.Operations.WidestCoord

@[expose] public section

/-!
# Splitting one box of a list

Lines 11-16 of [1, Alg. 1]: box `i` is replaced by its first half along its widest coordinate and
the second half is appended as box `k`, so no other box moves. A list without box `i`, or a box
without coordinates, is left as it is.

## Inputs
* `i` – box index
* `l` – list of boxes

## Output
* list with that box halved along its widest coordinate

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.splitAt (i : ℕ) (l : List (Fin n → Interval ℝ)) : List (Fin n → Interval ℝ)
    :=
  match l[i]? with
  | none => l
  | some B => match Taylm.widestCoord B with
    | none => l
    | some β => l.set i (Taylm.halveBox B β).1 ++ [(Taylm.halveBox B β).2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
