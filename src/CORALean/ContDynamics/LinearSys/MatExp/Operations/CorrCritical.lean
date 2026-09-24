import CORALean.ContSet.Interval.Real.Interval

/-!
# The correction's critical point

`corrCritical`: where [1]'s `s ↦ s ^ i - s` bottoms out: `i ^ (-1/(i-1))`, the only stationary
point, and the minimum because the map is convex.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Where `s ↦ s ^ i - s` bottoms out: `i ^ (-1/(i-1))`, the only stationary
point, and the minimum because the map is convex. -/
noncomputable def MatExp.corrCritical (i : ℕ) : ℝ :=
  (i : ℝ) ^ (-(1:ℝ) / ((i : ℝ) - 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
