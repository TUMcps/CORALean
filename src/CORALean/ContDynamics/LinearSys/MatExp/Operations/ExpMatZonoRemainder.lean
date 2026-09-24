import CORALean.ContSet.Zonotope.Real.Instances

/-!
# Matrix zonotopes: a uniform-width box

`expMatZonoRemainder`: [1, Sec. 3.3.2]'s tail, a box of uniform width `b` as a matrix
zonotope: centre zero, and one generator per entry carrying `b` there and nothing else.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A box of uniform width `b` as a matrix zonotope: centre zero, and one
generator per entry carrying `b` there and nothing anywhere else. -/
noncomputable def MatExp.expMatZonoRemainder (m : ℕ) (b : ℝ) : Zonotope (Mat ℝ m m) where
  h := m * m
  c := 0
  G := fun k i j => if finProdFinEquiv (i, j) = k then b else 0

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
