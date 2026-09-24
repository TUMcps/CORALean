import CORALean.ContSet.Interval.Real.Interval

/-!
# The second-order Taylor term's diagonal factor

`quadTerm`: the `γ` of [1, Lemma 3.1]: what a diagonal entry contributes through itself, and
the one place a variable occurs twice.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `γ` of [1, Lemma 3.1]: what a diagonal entry contributes through itself,
and the one place a variable occurs twice. -/
noncomputable def MatExp.quadTerm (t a : ℝ) : ℝ := a * t + a ^ 2 * t ^ 2 / 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
