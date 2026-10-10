import CORALean.ContSet.Interval.Real.Operations.Or

/-!
# `Location.guardIntersectLevelSet`, the box it intersects

CORA's `location/guardIntersect_levelSet`, Steps 2 and 3 of [1, Sec. 3.2]: each reach set's
box `interval(R{i})`, tightened by the contractor `tightenDomain` against the guard, and the
hull `|` of all of them. CORA wraps the contractor in a `try`, which keeps the box for a guard
with `<=`; the identity is a contractor for every guard, so `contract` covers both. Step 4,
`and_(guard, polyZonotope(I), 'approx')`, drops mixed second-order terms of the guard
(FINDINGS.md, `LevelSet and_, solvable polynomial zonotope`), and is replaced by [1, Prop. 1]
(`guardIntersectSolvable`) or [1, Prop. 2] (`guardIntersectUnsolvable`) on this box. The
reach sets come as their boxes.

## References

* [1] N. Kochdumper and M. Althoff. "Reachability Analysis for Hybrid Systems with Nonlinear
      Guard Sets". In Proc. of the 23rd ACM International Conference on Hybrid Systems:
      Computation and Control (HSCC), 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- [1, Sec. 3.2], Steps 2-3: the hull of the boxes `R₀ :: Rs` of the reach sets, each
tightened by `contract`. -/
def Location.guardIntersectLevelSet
    (contract : Real.Interval (Vec ℝ n) → Real.Interval (Vec ℝ n))
    (R₀ : Real.Interval (Vec ℝ n)) (Rs : List (Real.Interval (Vec ℝ n))) :
    Real.Interval (Vec ℝ n) :=
  let I_ : Real.Interval (Vec ℝ n) → Real.Interval (Vec ℝ n) := contract  -- tightenDomain
  Rs.foldl (fun I R => I.or (I_ R)) (I_ R₀)                                -- I = I | I_

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
