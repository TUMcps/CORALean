import CORALean.Real.MatSet.IntervalMat.IntervalMat

/-!
# What `IntervalMat` instantiates

`MatSet` only: an interval matrix denotes matrices, so it is the argument of an
operation and never the result of one.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

instance : MatSet IntervalMat := ⟨IntervalMat.construct⟩

@[simp] theorem IntervalMat.denote_eq {m n : ℕ} (IM : IntervalMat m n) :
    MatSet.denote IM = IM.construct := rfl

end CORALean.Real
