module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound

@[expose] public section

/-!
# An admissible truncation order

`IsOrderAdmissible x ε η`: the order `η` of the Taylor series of `e^x` is admissible at the error
`ε` when `2 ≤ η`, `expRemainderBound x η` is below `ε`, and `‖x‖ / (η + 2) < 1`. The conjuncts have
different sources. The last is the side condition `‖𝒜‖∞t/(p+2) < 1` that [1, Thm. 1] states for its
geometric-series bound on the remainder; [2] writes the remainder as an infinite series and needs
none. The second is CORALean's rendering of [2]'s tuning to an admissible error, applied to the
order; [2] only cites Bickart for the order. `2 ≤ η` is from no paper: `MatExp.expm_outer` and the
guarantee of `MatExp.intervalCorrectionMatrix` need it.

## Inputs
* `x` – matrix
* `ε` – admissible error
* `η` – Taylor order

## Output
* proposition that the order is admissible at the error

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
* [2] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning for reachability
      analysis of linear systems". 2020 59th IEEE Conference on Decision and Control (CDC), 2020.
-/

-- Authors:       Claude Sonnet 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An order meeting the admissible error `ε` at `x`: at least `2`, its bound under `ε`, and
`‖x‖ / (η + 2) < 1`, the side condition of [1, Thm. 1] that makes that bound mean anything. -/
def MatExp.IsOrderAdmissible (x : Mat ℝ n n) (ε : ℝ) (η : ℕ) : Prop :=
  2 ≤ η ∧ MatExp.expRemainderBound x η < ε ∧ ‖x‖ / ((η : ℝ) + 2) < 1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
