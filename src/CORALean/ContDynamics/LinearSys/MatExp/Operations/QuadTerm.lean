module

public import CORALean.ContSet.Interval.Real.Interval

@[expose] public section

/-!
# The second-order Taylor term's diagonal factor

`quadTerm`: the `γ` of [1, Prop. 4]: what a diagonal entry contributes through itself, and
the one place a variable occurs twice.

## Inputs
* `t` – time
* `a` – diagonal entry

## Output
* diagonal factor of the second-order Taylor term

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties, 2011.
-/

-- Authors:       Claude Sonnet 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The `γ` of [1, Prop. 4]: what a diagonal entry contributes through itself,
and the one place a variable occurs twice. -/
noncomputable def MatExp.quadTerm (t a : ℝ) : ℝ := a * t + a ^ 2 * t ^ 2 / 2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
