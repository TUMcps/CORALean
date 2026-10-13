import CORALean.ContSet.Taylm.Real.Operations.InvRemS
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The recursion gives the exact remainder

[1, Eq. 36–37], read as CORA reads them: `a·S_q(x)`, `a = (q+1)(-1)^{q+1}`, is the
remainder `1/x - Σₖ₌₀^q (-1)ᵏ (x - c)ᵏ / cᵏ⁺¹` of `1/x`'s Taylor polynomial at `c`, which is eq.
(34)'s integral by Taylor's theorem. With `Rⱼ₋₁` taken as eq. (34) at order `j - 1`, as printed,
the recursion would be `R_q = (-1)^{q+1}(x - c)^q/c^{q+1} + R_{q-1}` instead.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.invRemS_eq {c : ℝ} (hc : c ≠ 0) (x : ℝ) (q : ℕ) :
    ((q : ℝ) + 1) * (-1) ^ (q + 1) * Taylm.invRemS c q x
      = x⁻¹ - ∑ k ∈ Finset.range (q + 1),
        (-1) ^ k * (x - c) ^ k / c ^ (k + 1) := by -- --- PROOF ---
  induction q with
  | zero => simp [Taylm.invRemS]
  | succ j ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ← ih]
    simp only [Taylm.invRemS]
    push_cast
    have h1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((j : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
