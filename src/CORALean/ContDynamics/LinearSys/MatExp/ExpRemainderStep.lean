import CORALean.ContDynamics.LinearSys.MatExp.Enclosures

/-!
# Choosing the step size from an admissible error

The second knob of [1], the same way `ExpRemainderOrder` is the first: given an
order and an admissible error `ε`, `expRemainderStep` names a positive step
whose contribution `r · expRemainderBound (r • A) η` — the radius of
`inputRemainder` — stays under `ε`, and whose side condition holds too.

`Classical.choose` rather than a least element: the admissible steps are an
interval open at `0`, so there is no least one to name and minimality has no
counterpart here. Where no step meets `ε`, which `0 < ε` rules out, the junk
branch is `1`.

**This is not adaptive reachability.** `ε` bounds what the truncated orders of
the *exponential* contribute over a step, not the error of the reachable set,
and [1] tunes more knobs than this one and the order, splitting a stated error
between them.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

/-- A step meeting the admissible error `ε` at order `η`: positive, its
contribution under `ε`, and the side condition at the scaled matrix. -/
def MatExp.StepAdmissible (A : Mat ℝ n n) (η : ℕ) (ε : ℝ) (r : ℝ) : Prop :=
  0 < r ∧ r * MatExp.expRemainderBound (r • A) η < ε ∧ ‖r • A‖ / ((η : ℝ) + 2) < 1


-- =====================================  MAIN DEFINITION  ====================================== --

open scoped Classical in
/-- A step meeting `ε` at order `η`, and `1` where none does — which `0 < ε`
rules out, `expRemainderStep_spec` being stated under exactly that. -/
noncomputable def MatExp.expRemainderStep (A : Mat ℝ n n) (η : ℕ) (ε : ℝ) : ℝ :=
  if h : ∃ r : ℝ, MatExp.StepAdmissible A η ε r then h.choose else 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
