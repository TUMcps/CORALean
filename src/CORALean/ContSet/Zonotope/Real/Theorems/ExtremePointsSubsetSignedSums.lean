module

public import CORALean.ContSet.Zonotope.Real.Theorems.ConvexHullSignedSums
public import Mathlib.Analysis.Convex.Extreme

@[expose] public section

/-!
# The vertices of a zonotope are among `Z±(R)`

[1, Prop. 6.1, Eq. 38]: `V(Z(R)) ⊆ Z±(R)`, an extreme point of a convex hull of a set is in the
set. The converse fails (a point of `Z±(R)` need not be a vertex), which is why [1] speaks of
"potential vertices".

## References

* [1] M. Maïga, N. Ramdani, L. Travé-Massuyès and C. Combastel. "A Comprehensive Method for
      Reachability Analysis of Uncertain Nonlinear Hybrid Systems". IEEE Transactions on
      Automatic Control, 61(9):2341-2356, 2016.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n p : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.extremePoints_subset_signedSums (R : Fin p → Vec ℝ n) :
    Set.extremePoints ℝ (⟨p, 0, R⟩ : Zonotope (Vec ℝ n)).construct ⊆ Zonotope.signedSums R := by
  rw [← Zonotope.convexHull_signedSums]
  exact extremePoints_convexHull_subset

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
