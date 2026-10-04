import Mathlib.Data.Finset.Lattice.Fold

/-!
# Outlier removal by searching over boundary points

[1, Sec. 5.1.1]: a search tree rooted at the identification problem, each child removing one
boundary point of its parent's problem, `n_out` layers deep; the leaf of lowest cost names the
outliers. `cost S` is the optimal cost of the program (19) or (20) on the points `S`, `bd S`
the boundary points of its solution ([1, Prop. 8] computes them): both are a solver's, and
arguments here. A node without boundary points is a leaf: no single removal lowers its cost.
The value is the least leaf cost; `searchOutliers_optimal` proves it the least cost over all
removals of at most `n_out` points. Written over any linear order, so it runs at whatever
scalar the costs come in.

## References

* [1] L. Lützow, M. Eichelbeck, M. J. Kochenderfer and M. Althoff. "Zono-Conformal
      Prediction: Zonotope-Based Uncertainty Quantification for Regression and
      Classification Tasks". Journal of Machine Learning Research, 26(294):1-37, 2025.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 5.1.1]: the least cost over the leaves of the boundary-point search tree. -/
def Conform.searchOutliers {P β : Type} [DecidableEq P] [LinearOrder β] (cost : Finset P → β)
    (bd : Finset P → Finset P) : ℕ → Finset P → β
  | 0, S => cost S
  | k + 1, S =>
    let children := bd S
    if h : children.Nonempty then
      children.inf' h fun b => Conform.searchOutliers cost bd k (S.erase b)
    else cost S

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
