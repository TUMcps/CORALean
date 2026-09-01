import CORALean.ContSet.Interval.Real.Theorems.API

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

namespace CORALean.Real

variable {n : ℕ}

instance : ContSet (Interval n) (Vec ℝ n) := ⟨Interval.construct⟩

instance : OuterContSet (Interval n) (Vec ℝ n) where
  plus := Interval.plus
  linComb := Interval.linComb
  reduce I _ := I
  plus_outer := Interval.plus_outer
  linComb_outer := Interval.linComb_outer
  reduce_outer _ _ := subset_rfl

instance : Mtimes (Mat ℝ) Interval where
  mtimes := Interval.mtimes
  mtimes_outer M I := by
    simp only [ContSet.construct_mat, Scalar.toRealMat_real, Set.biUnion_singleton]
    exact Interval.mtimes_outer M I

end CORALean.Real
