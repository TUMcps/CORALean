module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTerm

@[expose] public section

/-!
# The second-order Taylor term's diagonal factor, least value on a box

`quadTermLo`: the least value [1, Prop. 4]'s `quadTerm t` takes on `[a, b]`. `-1/t` is the
vertex; where `t = 0` the `if` reads `-1/t` as `0` and this is sound but not tight.

## Inputs
* `t` – time
* `a` – box lower end
* `b` – box upper end

## Output
* least value of the diagonal factor on the box

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

/-- The least value `quadTerm t` takes on `[a, b]`. `-1/t` is the vertex; where
`t = 0` the `if` reads `-1/t` as `0` and this is sound but not tight. -/
noncomputable def MatExp.quadTermLo (t a b : ℝ) : ℝ :=
  if a ≤ -1 / t ∧ -1 / t ≤ b then -(1 / 2)
  else min (MatExp.quadTerm t a) (MatExp.quadTerm t b)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
