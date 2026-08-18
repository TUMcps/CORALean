import CORALean.Arithmetic.Real.ContSet.Interval.Theorems

/-!
# What `Interval` instantiates

The class fields *are* the obligations, so there is nothing to restate.

`reduce` is the identity: an interval holds two bounds per coordinate whatever
order is asked for, so it has nothing to give up.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

variable {n : ℕ}

instance : ContSet (Interval n) n := ⟨Interval.construct⟩

instance : OuterContSet Interval ℝ where
  plus := Interval.plus
  mtimes := Interval.mtimes
  reduce I _ := I
  plus_outer := Interval.plus_outer
  mtimes_outer := Interval.mtimes_outer
  reduce_outer _ _ := subset_rfl

end CORALean.Arithmetic.Real
