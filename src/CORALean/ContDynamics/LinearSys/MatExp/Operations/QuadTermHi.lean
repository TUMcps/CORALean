import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTerm

/-!
# The second-order Taylor term's diagonal factor, greatest value on a box

`quadTermHi`: the greatest value [1, Lemma 3.1]'s `quadTerm t` takes on `[a, b]`, always at
an endpoint since the parabola opens upwards.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Sonnet 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The greatest, always at an endpoint: the parabola opens upwards. -/
noncomputable def MatExp.quadTermHi (t a b : ℝ) : ℝ :=
  max (MatExp.quadTerm t a) (MatExp.quadTerm t b)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
