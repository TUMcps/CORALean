import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Interval.Set.Defs

/-!
# What a root search owes a contractor

[1, Sec. 3 (three cases)] moves the left bound of `[x̲, x̅]` to the smallest root of an extremal
function, found by `BoxNarrow` or, below degree four, in closed form. The contraction uses one
property of that root and no other: before it the function has no zero in `[x̲, x̅]`.
`IsLeftRootBound` asks exactly that of a search, for every function continuous on the domain,
and `IsRightRootBound` is its mirror image. A search returning the smallest root has it; one
returning a value past `x̅` says the domain holds no root at all.

## References

* [1] G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". In Proc. of the 16th International Conference on Principles
      and Practice of Constraint Programming (CP 2010), LNCS 6308, pp. 491-498, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `root g lo hi` leaves no zero of a continuous `g` in `[lo, hi]` to its left. -/
def Interval.IsLeftRootBound (root : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop :=
  ∀ g lo hi, ContinuousOn g (Set.Icc lo hi) →
    ∀ z ∈ Set.Icc lo hi, z < root g lo hi → g z ≠ 0

/-- `root g lo hi` leaves no zero of a continuous `g` in `[lo, hi]` to its right. -/
def Interval.IsRightRootBound (root : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop :=
  ∀ g lo hi, ContinuousOn g (Set.Icc lo hi) →
    ∀ z ∈ Set.Icc lo hi, root g lo hi < z → g z ≠ 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
