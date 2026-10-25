module

public import CORALean.ContSet.Interval.Real.Interval
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The second-order Taylor term, exactly, at one matrix

`expW`: [1, Prop. 4]'s `W(t) = M t + ½ M² t²` at one matrix, which is orders one and two
of `expTaylor (t • M)`.

## Inputs
* `M` – matrix
* `t` – time

## Output
* second-order Taylor term of the exponential at the matrix

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

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `W(t) = M t + ½ M² t²` at one matrix, which is orders one and two of
`expTaylor (t • M)`. -/
noncomputable def MatExp.expW (M : Mat ℝ n n) (t : ℝ) : Mat ℝ n n :=
  t • M + (t ^ 2 / 2) • (M * M)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
