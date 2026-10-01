import CORALean.ContSet.Zonotope.Real.Operations.ReduceGirard
import CORALean.ContSet.Zonotope.Real.Theorems.ReduceByOuter

/-!
# Girard's reduction over-approximates

Girard's interval-hull argument [1, Sec. 3.4]. Two cases: below the order there is
nothing to do, and above it the rule is a partition like any other, so
`reduceBy_outer` closes it. Girard's metric appears
nowhere — that is the point of stating the enclosure at an arbitrary partition.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.reduceGirard_outer (Z : Zonotope (Vec ℝ n)) (o : ℕ) :
    Z.construct ⊆ (Z.reduceGirard o).construct := by
  unfold Zonotope.reduceGirard
  split_ifs with hlt
  · exact Zonotope.reduceBy_outer Z _
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
