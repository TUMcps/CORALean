import CORALean.Specification.STL.Definitions.BranchHolds
import CORALean.Specification.STL.Theorems.ShiftShift

/-!
# A raised power reads the shifted trace

`X_c^{j+1}` of a branch at `ξ` is `X_c^j` of it at `⟨ξ⟩_c`: how [1, Sec. 4.1]'s `X_c(⋁ⱼ X_c^j …) ≡
⋁ⱼ X_c^{j+1} …` moves a clause.

## References

* [1] H. Roehm, J. Oehlerking, T. Heinz and M. Althoff. "STL Model Checking of Continuous and
      Hybrid Systems". ATVA, LNCS 9938, pp. 412-427, 2016.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped NNReal

variable {X : Type}


-- =======================================  MAIN THEOREM  ======================================= --

theorem STL.Branch.holds_shift (c : ℝ≥0) (b : STL.Branch X) (ξ : ℝ≥0 → X) :
    ({ b with j := b.j + 1 } : STL.Branch X).Holds c ξ ↔ b.Holds c (Time.shift ξ c) := by
  -- the argument `t + (j + 1) c` is `t + j c + c`
  have e₀ : ((b.j + 1 : ℕ) : ℝ≥0) * c = b.j * c + c := by push_cast; ring
  unfold STL.Branch.Holds
  simp only [Time.shift, e₀, add_assoc]


end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
