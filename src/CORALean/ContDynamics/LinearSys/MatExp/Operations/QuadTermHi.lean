module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTerm

@[expose] public section

/-!
# The second-order Taylor term's diagonal factor, greatest value on a box

`quadTermHi`: the greatest value [1, Prop. 4]'s `quadTerm t` takes on `[a, b]`, always at
an endpoint since the parabola opens upwards.

## Inputs
* `t` – time
* `a` – box lower end
* `b` – box upper end

## Output
* greatest value of the diagonal factor on the box

## References

* [1] M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear
      Dynamic Systems with Parametric Uncertainties". In A. Rauh and E. Auer (eds.),
      Modeling, Design, and Simulation of Systems with Uncertainties, Springer, 2011.
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
