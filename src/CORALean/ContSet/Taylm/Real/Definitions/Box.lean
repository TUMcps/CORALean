module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# Boxes

A box of `n` coordinates is a pair of bounds per coordinate, the `[x]` that [1, Alg. 1] splits;
`IsInBox` is membership, and `Covers X l` says the boxes `l` together contain `X`, the invariant
branch and bound keeps.

## Inputs
* `B` – box
* `t` – point

## Output
* proposition that the point lies in the box

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

/-- `t` lies in the box `B`, coordinate by coordinate. -/
def Taylm.IsInBox (B : Fin n → Interval ℝ) (t : Vec ℝ n) : Prop := ∀ k, (B k).inf ≤ t k ∧
    t k ≤ (B k).sup

/-- Every point of `X` lies in one of the boxes `l`. -/
def Taylm.Covers (X : Fin n → Interval ℝ) (l : List (Fin n → Interval ℝ)) : Prop :=
  ∀ t, Taylm.IsInBox X t → ∃ B ∈ l, Taylm.IsInBox B t

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
