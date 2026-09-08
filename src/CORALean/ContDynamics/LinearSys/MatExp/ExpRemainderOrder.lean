import CORALean.ContDynamics.LinearSys.MatExp.Enclosures

/-!
# Choosing the truncation order from an admissible error

[1] tunes a reachability run's parameters to an error the caller states rather
than to numbers the caller guesses. This is that choice for one knob: given `ε`,
`expRemainderOrder` names an order whose remainder bound is under `ε`, and the
least such order, so it is a tuning rule and not an arbitrary pick.

`OrderAdmissible` carries the soundness side condition `‖x‖/(η+2) < 1` beside
the error — without it `expRemainderBound` is meaningless rather than merely
loose — and `2 ≤ η`, the form every step theorem here takes.

`sInf` over ℕ is `Nat.find` under classical decidability, which is what makes
this noncomputable: no `Decidable` instance for a strict inequality between
reals exists at this layer.

**This is not adaptive reachability.** `ε` bounds the *matrix exponential's*
remainder, not the error of the reachable set the enclosure denotes, and [1]
tunes the step size and the zonotope order besides.

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

/-- An order meeting the admissible error `ε` at `x`: at least `2`, its bound
under `ε`, and the side condition that makes that bound mean anything. -/
def MatExp.OrderAdmissible (x : Mat ℝ n n) (ε : ℝ) (η : ℕ) : Prop :=
  2 ≤ η ∧ MatExp.expRemainderBound x η < ε ∧ ‖x‖ / ((η : ℝ) + 2) < 1


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The least order meeting `ε`, and `0` where none does — which `0 < ε` rules
out, `expRemainderOrder_spec` being stated under exactly that. -/
noncomputable def MatExp.expRemainderOrder (x : Mat ℝ n n) (ε : ℝ) : ℕ :=
  sInf {η : ℕ | MatExp.OrderAdmissible x ε η}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
