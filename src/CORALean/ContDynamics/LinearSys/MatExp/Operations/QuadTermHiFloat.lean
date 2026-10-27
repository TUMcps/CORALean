module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.QuadTermFloat

@[expose] public section

/-!
# The second-order Taylor term's diagonal factor, greatest value on a box, in floats

`quadTermHi`: `Real.MatExp.quadTermHi` of [1, Prop. 4] rounded up. The parabola opens
upwards, so the greatest value on `[a, b]` is at an endpoint, and the larger of the two endpoint
upper bounds is one.

## Inputs
* `t` – float time
* `a` – float box lower end
* `b` – float box upper end

## Output
* float upper bound of the diagonal factor on the box

## References

* [1] [M. Althoff, B. H. Krogh and O. Stursberg. "Analyzing Reachability of Linear Dynamic Systems
      with Parametric Uncertainties". Modeling, Design, and Simulation of Systems with
      Uncertainties,
      2011.](../../../../../../references/2011/althoff-reachability-parametric-uncertainties.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       08-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The greater of `γ`'s two endpoint upper bounds. -/
def MatExp.quadTermHi (t a b : 𝕋) : 𝕋 :=
  maximum (MatExp.quadTerm t a).sup (MatExp.quadTerm t b).sup

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
