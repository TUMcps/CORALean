module

public import CORALean.Global.Tensor
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section

/-!
# The `1`-norm against the supremum norm

`[1, Eq. 30]` bounds the `1`-circumradius of the parallelotope `Π` by `n` times
its `∞`-circumradius, `R₁(Π) ≤ n R∞(Π)`, through `‖x‖₁ ≤ n ‖x‖∞` — which holds, pointwise,
on any set. Its first step, `R₁(Π) = maxᵢ ‖vᵢ‖₁`, does not
(`l1_norm_le_card_mul_norm_counterexample`); only this inequality is used afterwards.

## Inputs
* `x` – vector

## Hypotheses
* none

## Conclusion
* the 1-norm is at most the dimension times the supremum norm

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem l1_norm_le_card_mul_norm (x : Vec ℝ n) : ∑ i, |x i| ≤ n * ‖x‖ := by
  calc ∑ i, |x i| ≤ ∑ _i : Fin n, ‖x‖ :=
        Finset.sum_le_sum fun i _ => by simpa using norm_le_pi_norm x i
    _ = n * ‖x‖ := by simp

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
