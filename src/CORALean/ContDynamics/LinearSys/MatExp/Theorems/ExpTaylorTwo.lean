module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpW
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpTaylor
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# The second-order truncation is `I + W(t)`

What ties [1, Lemma 3.1] to [1, Thm. 3.2]: orders zero to two of
`expTaylor (t • M)` are `I` plus the `W(t)` of the lemma, so replacing those
three orders by `expIntervalW` replaces exactly the part the lemma is about.

Proved entrywise, `(t • M) ^ 2 = t ² • (M * M)` having been taken out first:
the scalars are then real numbers and `ring` closes it, where the matrix-level
identity would have to be assembled from `smul` lemmas by hand.

## Inputs
* `M` – matrix
* `t` – time

## Hypotheses
* none

## Conclusion
* the second-order truncation is the identity plus the second-order term

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The Taylor truncation at order two is the identity plus `W(t)`. -/
theorem MatExp.expTaylor_two (M : Mat ℝ n n) (t : ℝ) : -- --- CONCL ---
    MatExp.expTaylor (t • M) 2 = 1 + MatExp.expW M t := by -- --- PROOF ---
  have hx2 : (t • M) ^ 2 = (t ^ 2) • (M * M) := by
    rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, sq]
  rw [MatExp.expTaylor, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    pow_zero, pow_one, hx2, MatExp.expW, Nat.factorial_zero, Nat.factorial_one,
    Nat.factorial_two]
  -- entrywise the scalars are reals again, so `ring` can finish
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
