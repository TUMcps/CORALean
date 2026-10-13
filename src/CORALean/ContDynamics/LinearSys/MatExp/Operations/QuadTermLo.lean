import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTerm

/-!
# The second-order Taylor term's diagonal factor, least value on a box

`quadTermLo`: the least value [1, Lemma 3.1]'s `quadTerm t` takes on `[a, b]`. `-1/t` is the
vertex; where `t = 0` the `if` reads `-1/t` as `0` and this is sound but not tight.

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

/-- The least value `quadTerm t` takes on `[a, b]`. `-1/t` is the vertex; where
`t = 0` the `if` reads `-1/t` as `0` and this is sound but not tight. -/
noncomputable def MatExp.quadTermLo (t a b : ℝ) : ℝ :=
  if a ≤ -1 / t ∧ -1 / t ≤ b then -(1 / 2)
  else min (MatExp.quadTerm t a) (MatExp.quadTerm t b)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
