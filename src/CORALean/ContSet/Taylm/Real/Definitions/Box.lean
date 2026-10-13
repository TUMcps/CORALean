import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic

/-!
# Boxes

A box of `n` coordinates is a pair of bounds per coordinate, the `[x]` that [1, Alg. 1] splits;
`InBox` is membership, and `Covers X l` says the boxes `l` together contain `X`, the invariant
branch and bound keeps.

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

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `t` lies in the box `B`, coordinate by coordinate. -/
def Taylm.InBox (B : Fin n → ℝ × ℝ) (t : Vec ℝ n) : Prop := ∀ k, (B k).1 ≤ t k ∧ t k ≤ (B k).2

/-- Every point of `X` lies in one of the boxes `l`. -/
def Taylm.Covers (X : Fin n → ℝ × ℝ) (l : List (Fin n → ℝ × ℝ)) : Prop :=
  ∀ t, Taylm.InBox X t → ∃ B ∈ l, Taylm.InBox B t

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
