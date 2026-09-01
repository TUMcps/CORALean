import CORALean.MatSet.IntervalMat.IntervalMat

/-!
# What `IntervalMat` instantiates

`ContSet` at `Mat ℝ m n`: an interval matrix denotes matrices, so it is the
argument of an operation and never the result of one, and it carries no
`OuterContSet`.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   01-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {m n : ℕ}

instance : ContSet (IntervalMat m n) (Mat ℝ m n) := ⟨IntervalMat.construct⟩

@[simp] theorem IntervalMat.construct_eq (IM : IntervalMat m n) :
    ContSet.construct IM = IM.construct := rfl

end CORALean.Real
