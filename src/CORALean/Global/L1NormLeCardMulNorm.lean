import CORALean.Global.Tensor
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The `1`-norm against the supremum norm

`[1, Eq. 30]` bounds the `1`-circumradius of the parallelotope `Π` by `n` times
its `∞`-circumradius, `R₁(Π) ≤ n R∞(Π)`, through `‖x‖₁ ≤ n ‖x‖∞` — which holds, pointwise,
on any set. Its first step, `R₁(Π) = maxᵢ ‖vᵢ‖₁`, does not
(`l1_norm_le_card_mul_norm_counterexample`); only this inequality is used afterwards.

## References

* [1] A. Kulmburg and M. Althoff. "On the co-NP-Completeness of the Zonotope Containment
      Problem". European Journal of Control, 62:84-91, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


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
